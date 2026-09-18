module

public import Lean.Data.Json
public import Canonical.Canonical2.Util

open Lean Json

public section

namespace Canonical2

/-- USD price per 1M tokens. -/
structure Pricing where
  input : Float := 0.0
  output : Float := 0.0

inductive Provider where
| Llama (url : String)
| Vllm (url : String) (model : String)
| Gemini (key : String) (model : String := "gemini-3-flash-preview") (effort : String := "low")
        (pricing : Pricing := { input := 1.50, output := 9.00 })
| Claude (model : String := "claude-haiku-4-5-20251001") (effort : String := "medium") /- CLI -/
| Codex (model : String := "gpt-5.6-luna") (effort : String := "medium") /- CLI -/

structure LLMConfig where
  temperature : Float
  maxTokens : Nat

def Provider.cost (provider : Provider) (usage : Json) : Float :=
  match provider with
  | .Gemini _ _ _ p =>
    -- Gemini's OpenAI-compat usage excludes thinking tokens from
    -- `completion_tokens` but counts them in `total_tokens`; they're billed at
    -- the output rate. So the billable output is `total - prompt` (visible
    -- output + thinking), falling back to `completion_tokens` if total is absent.
    let nat (key : String) : Nat := (usage.getObjValAs? Nat key).toOption.getD 0
    let prompt := nat "prompt_tokens"
    let output := max (nat "completion_tokens") ((nat "total_tokens") - prompt)
    (prompt.toFloat * p.input + output.toFloat * p.output) / 1000000.0
  | _ => 0.0


structure Function where
  name : String
  arguments : String -- encoding Json
deriving ToJson

structure ToolCall where
  id : String
  type : String := "function"
  function : Function
deriving ToJson

structure Message where
  role : String
  content : String
  tool_call_id : Option String := none
  tool_calls : Array ToolCall := #[]
deriving Inhabited

instance : ToJson Message where
  toJson m := Json.mkObj <|
    [("role", Json.str m.role), ("content", Json.str m.content)] ++
    (m.tool_call_id.map ("tool_call_id", Json.str ·)).toList ++
    (if m.tool_calls.isEmpty then [] else [("tool_calls", toJson m.tool_calls)])

structure Response where
  message : Message
  session : Option String
  cost : Float

def defaultConfig : Provider → LLMConfig
| .Llama _ => ⟨0.3, 1024⟩
| .Vllm _ _ => ⟨0.3, 1024⟩
| _ => ⟨0.3, 4096⟩

variable (log : String → String → IO Unit)

private def ToolCall.appendDelta (tc : ToolCall) (delta : Json) : IO ToolCall := do
  let mut tc := tc
  if let .ok id := delta.getObjValAs? String "id" then
    tc := { tc with id := id }
  if let .ok f := delta.getObjVal? "function" then
    if let .ok n := f.getObjValAs? String "name" then
      tc := { tc with function.name := n }
    if let .ok a := f.getObjValAs? String "arguments" then
      log "token" a
      tc := { tc with function.arguments := tc.function.arguments ++ a }
  return tc

private def Message.appendDelta (msg : Message) (delta : Json) : IO Message := do
  let mut msg := msg
  if let .ok content := delta.getObjValAs? String "content" then
    log "thinking" content
    msg := { msg with content := msg.content ++ content }
  if let .ok deltas := delta.getObjVal? "tool_calls" >>= (·.getArr?) then
    for td in deltas do
      let idx := (td.getObjValAs? Nat "index").toOption.getD 0
      let calls := msg.tool_calls.rightpad (idx + 1)
        { id := "", function := { name := "", arguments := "" } }
      msg := { msg with tool_calls := ← calls.modifyM idx (·.appendDelta log td) }
  return msg

private def Response.chatCompletionsUpdate (response : Response)
  (provider : Provider) (line : String) : IO Response := do
  if let .ok err := Json.parse line >>= (·.getObjVal? "error") then
    log "error" err.compress
    throw (IO.userError err.compress)
  let some payload := line.dropPrefix? "data: " | return response
  let .ok j := (Json.parse payload.toString) | return response
  let mut response := response
  if let .ok choices := j.getObjVal? "choices" >>= (·.getArr?) then
    if let some choice := choices[0]? then
      if let .ok delta := choice.getObjVal? "delta" then
        response := { response with message := ← response.message.appendDelta log delta }
  if let .ok usage := j.getObjVal? "usage" then
    let newCost := provider.cost usage
    log "cost" s!"{newCost - response.cost}"
    response := { response with cost := newCost }
  return response

private def Response.applyClaudeEvent (response : Response)
  (event : Json) (log : String → String → IO Unit) : ExceptT String IO Response := do
  match ← event.getObjValAs? String "type" with
  | "content_block_start" =>
    let cb ← event.getObjVal? "content_block"
    if let "tool_use" ← cb.getObjValAs? String "type" then
      let id ← cb.getObjValAs? String "id"
      return { response with message := { response.message with
        tool_calls := response.message.tool_calls.push
          { id, function := { name := "have", arguments := "" } } } }
  | "content_block_delta" =>
    let delta ← event.getObjVal? "delta"
    let deltaType ← delta.getObjValAs? String "type"
    if deltaType == "input_json_delta" then
      let chunk ← delta.getObjValAs? String "partial_json"
      log "token" chunk
      let calls := response.message.tool_calls
      return { response with message := { response.message with
        tool_calls := calls.modify (calls.size - 1) fun tc =>
          { tc with function.arguments := tc.function.arguments ++ chunk } } }
    if deltaType == "thinking_delta" then
      let thinking ← delta.getObjValAs? String "thinking"
      log "thinking" thinking
      return { response with message := { response.message with content := response.message.content ++ thinking } }
  | _ => pure ()
  return response

private def Response.claudeUpdate (response : Response) (line : String) : IO Response := do
  let .ok j := Json.parse line | return response
  let mut response := response
  if let .ok session := j.getObjValAs? String "session_id" then
    response := { response with session }
  match j.getObjValAs? String "type" with
  | .ok "stream_event" =>
    if let .ok event := j.getObjVal? "event" then
      response := (← response.applyClaudeEvent event log).toOption.getD response
  | .ok "assistant" =>
    if let .ok msg := j.getObjVal? "message" then
      if let .ok blocks := msg.getObjVal? "content" >>= (·.getArr?) then
        for block in blocks do
          let blockType := (block.getObjValAs? String "type").toOption.getD ""
          if blockType == "thinking" || blockType == "text" then
            let key := if blockType == "thinking" then "thinking" else "text"
            if let .ok text := block.getObjValAs? String key then
              log "thinking" text
              response := { response with message :=
                { response.message with content := response.message.content ++ text } }
          else if blockType == "tool_use" then
            if let .ok id := block.getObjValAs? String "id" then
              if let .ok input := block.getObjVal? "input" then
                let args := input.compress
                log "token" args
                response := { response with message := { response.message with
                  tool_calls := response.message.tool_calls.push
                    { id, function := { name := "have", arguments := args } } } }
  | .ok "result" =>
    if let .ok true := j.getObjValAs? Bool "is_error" then
      log "error" j.compress
      throw (IO.userError j.compress)
  | _ => pure ()
  return response

private def Response.codexUpdate (response : Response) (line : String) : IO Response := do
  let .ok j := Json.parse line | return response
  let mut response := response
  match j.getObjValAs? String "type" with
  | .ok "thread.started" =>
    if let .ok id := j.getObjValAs? String "thread_id" then
      response := { response with session := id }
  | .ok "item.completed" =>
    let .ok item := j.getObjVal? "item" | return response
    match item.getObjValAs? String "type", item.getObjValAs? String "text" with
    | .ok "reasoning", .ok text =>
      log "thinking" (text ++ "\n")
      response := { response with message := { response.message with content := response.message.content ++ text } }
    | .ok "agent_message", .ok text =>
      log "token" text
      response := { response with message := { response.message with
        tool_calls := response.message.tool_calls.push { id := "have", function := { name := "have", arguments := text } } } }
    | .ok "error", _ =>
      log "error" ((item.getObjValAs? String "message").toOption.getD item.compress)
    | _, _ => pure ()
  | .ok "error" | .ok "turn.failed" =>
    log "error" j.compress
    throw (IO.userError j.compress)
  | _ => pure ()
  return response

def Provider.updateResponse (response : Response)
  (line : String) (provider : Provider) : IO Response := do
  match provider with
  | .Llama _ | .Vllm _ _ | .Gemini _ _ _ _ =>
    response.chatCompletionsUpdate log provider line
  | .Claude _ _ => response.claudeUpdate log line
  | .Codex _ _ => response.codexUpdate log line

private def curlArgs (url : String) (extraPayload : List (String × Json))
    (extraHeaders : Array String) (config : LLMConfig) (messages : Array Message)
    (tools : Json) (constrained : Bool) : Array String :=
  let payload := extraPayload ++ [
    ("messages", toJson messages), ("tools", tools),
    ("tool_choice", Json.str (if constrained then "required" else "auto")),
    ("temperature", config.temperature.toJson),
    ("max_tokens", config.maxTokens), ("stream", true),
    ("stream_options", Json.mkObj [("include_usage", true)])
  ]
  #["-N", "-s", "-X", "POST", url, "-H", "Content-Type: application/json"] ++
    extraHeaders ++ #["-d", (Json.mkObj payload).compress]

def noThinking : String × Json :=
  ("chat_template_kwargs", Json.mkObj [("enable_thinking", Json.bool false)])

def STDIO_CONFIG : IO.Process.StdioConfig := { stdin := .null, stdout := .piped, stderr := .piped }

private def codexSchemaFile (tools : Json) : IO System.FilePath := do
  let file := (← cacheDir) / s!"codex-schema-{hash tools.compress}.json"
  unless ← file.pathExists do
    IO.FS.createDirAll (← cacheDir)
    IO.FS.writeFile file tools.compress
  return file

private def llmSpawn (provider : Provider) (config : LLMConfig) (messages : Array Message)
    (tools : Json) (constrained : Bool) (session : Option String) : IO (IO.Process.Child STDIO_CONFIG) := do
  let pending := (messages.toList.reverse.takeWhile (·.role != "assistant")).reverse
  let prompt := String.intercalate "\n\n" (pending.map (·.content))
  let cmd : IO.Process.SpawnArgs ← match provider with
  | .Claude m e =>
    let args := #["--system-prompt", "", "--tools", "", "--disable-slash-commands", "--strict-mcp-config",
      "--model", m, "--effort", e, "--output-format", "stream-json", "--verbose",
      "--include-partial-messages", "--json-schema", tools.compress]
    let args := match session with
      | some sid => args ++ #["--resume", sid, "-p", prompt]
      | none => args ++ #["-p", prompt]
    pure { cmd := "claude", args }
  | .Codex m e =>
    let args := #["--json", "--skip-git-repo-check", "-m", m,
      "-c", s!"model_reasoning_effort={e}", "-c", "model_reasoning_summary=detailed",
      "-c", "mcp_servers={}", "--output-schema", (← codexSchemaFile tools).toString]
    let args := match session with
      | some thread => #["exec", "resume"] ++ args ++ #[thread, prompt]
      | none => #["exec", "-s", "read-only"] ++ args ++ #[prompt]
    pure { cmd := "codex", args }
  | .Llama u =>
    pure { cmd := "curl", args := curlArgs u [noThinking] #[] config messages tools constrained }
  | .Vllm u m =>
    pure { cmd := "curl", args := curlArgs u [("model", Json.str m), noThinking] #[] config messages tools constrained }
  | .Gemini key m e _ =>
    let args := curlArgs
      "https://generativelanguage.googleapis.com/v1beta/openai/chat/completions"
      [("model", Json.str m), ("reasoning_effort", Json.str e)]
      #["-H", s!"Authorization: Bearer {key}"]
      config messages tools constrained
    pure { cmd := "curl", args }
  IO.Process.spawn { cmd with toStdioConfig := STDIO_CONFIG }

def llm (provider : Provider) (config : LLMConfig) (messages : Array Message)
    (tools : Json) (constrained : Bool) (session : Option String := none)
    : IO (CancelableTask (Except IO.Error Response)) := do
  let child ← llmSpawn provider config messages tools constrained session
  let cleanup : IO Unit := do
    try child.kill catch _ => pure ()
    try let _ ← child.wait catch _ => pure ()
  return { cancelPost := cleanup, task := ← IO.asTask do
    let mut response : Response := {
      message := { role := "assistant", content := "" }, session, cost := 0.0
    }
    let mut done := false
    let mut eof := false
    while !done do
      let line ← child.stdout.getLine
      response ← provider.updateResponse log response line
      eof := line.isEmpty
      done := eof || response.message.tool_calls.back?.any
        fun tc => (Json.parse tc.function.arguments).isOk
    if eof then
      let err ← child.stderr.readToEnd
      unless err.trimAscii.isEmpty do log "error" err.trimAscii.toString
    cleanup
    return response
  }
