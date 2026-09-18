module

public meta import Canonical.Canonical2.Rpc
public meta import Canonical.Canonical2.LLM
public meta import Canonical.Canonical2.Llama
public import Canonical.Canonical2.Basic
public import Lean.LibrarySuggestions.Basic

open Lean Meta Expr Elab Term Server Tactic Core RequestM IO LibrarySuggestions

public meta section

namespace Canonical2

def goalPremisesMessage (goal premises : String) : Message :=
  { role := "user", content := s!"Goal:\n```lean4\n{goal}\n```\n\nLibrary theorems:\n```lean4\n{premises}\n```" }

def subgoalPrompt (goal : String) (premises : String) : Provider → Array Message
| .Llama _ | .Vllm _ _ => Id.run do
  let [a, b, c] := (include_str "include/llama-prompt.md").splitOn "%" | panic! "llama-prompt.md formatting error."
  #[{ role := "user", content := a ++ goal ++ b ++ premises ++ c }]
| _ => #[{ role := "system", content := include_str "include/prompt.md" }, goalPremisesMessage goal premises]

/-- Decoded arguments of the `have` tool. Mirrors `haveSchema`. -/
structure Have where
  name : String
  type : String
  clear : Array String
deriving FromJson

def haveSchema (hyps : Array String) : Json := Json.mkObj [
    ("type", "object"),
    ("properties", Json.mkObj [
      ("name", Json.mkObj [
        ("type", "string"),
        ("description", "An identifier for the intermediate statement.")
      ]),
      ("type", Json.mkObj [
        ("type", "string"),
        ("description", "The type for the intermediate statement, as Lean 4 proposition without `have`.")
      ]),
      ("clear", Json.mkObj [
        ("type", "array"),
        ("items", Json.mkObj <| [("type", Json.str "string"), ("enum", Json.arr (hyps.map Json.str))]),
        ("default", Json.arr #[]),
        ("description", "Any hypotheses that are irrelevant for proving the goal.")
      ])
    ]),
    ("required", Json.arr #["name", "type", "clear"]),
    ("additionalProperties", Json.bool false)
  ]

def subgoalTools (hyps : Array String) : Provider → Json
| .Claude _ _ | .Codex _ _ => haveSchema hyps
| _ => Json.arr #[
    Json.mkObj [
      ("type", "function"),
      ("function", Json.mkObj [
        ("name", "have"),
        ("description", "Submit an intermediate subgoal."),
        ("parameters", haveSchema hyps)
      ])
    ]
  ]

structure RolloutDraft where
  mvarId : MVarId
  children : Array MVarId
  fvar : FVarId
  name : Name
  type : Expr
  typeString : String
  messages : Array Message
  tools : Json
deriving Inhabited

def premisesString (premises : Array Name) : MetaM String := do
  let arr ← (← premises.filterMapM fun x => do pure ((← getEnv).find? x)).mapM
    fun x => do pure s!"{x.name} : {← Meta.ppExpr x.type}\n"
  return String.join (arr.toList)

def checkDuplicate (mvar : MVarId) (type : Expr) : MetaM Unit := do
  withTransparency .none do
    let decl ← mvar.getDecl
    for x in decl.lctx do
      if ← isDefEqGuarded type x.type then
         throwError s!"This statement is a duplicate of hypothesis {x.userName}."
    let (metas, _, result) ← forallMetaTelescope type
    if ← isDefEqGuarded result decl.type then
      let mut seen : Std.HashSet FVarId := {}
      for m in metas do
        let some id := (← instantiateMVars m).fvarId? | return
        let (false, seen') := seen.containsThenInsert id | return
        seen := seen'
      throwError s!"This statement is a duplicate the goal."

def generate (log : String → String → IO Unit) (mvar : MVarId) (premises : Array Name)
  (provider : Provider) (config : LLMConfig := defaultConfig provider)
  (retries := if config.temperature == 0.0 then 1 else 3) (wait : UInt32 := 0) (stall := 0)
  (prompt : String := "") : MetaM (MetaTask RolloutDraft) := mvar.withContext do
  let llmRef : IO.Ref (Option (CancelableTask (Except IO.Error Response))) ← IO.mkRef none
  MetaM.toTask (cancel := do if let some t ← llmRef.get then t.cancel) do
    log "generate" ""
    IO.sleep wait
    if ← IO.checkCanceled then throwError "canceled."
    let start ← IO.monoMsNow
    let goal ← Meta.ppGoal mvar
    let premisesString ← premisesString premises[:12]
    let hyps : Array String := (← getLCtx).foldr (init := #[]) fun decl acc =>
      if decl.isImplementationDetail then acc else acc.push decl.userName.toString
    let tools := subgoalTools hyps provider
    let constrained := !provider matches .Llama _ && !provider matches .Vllm _ _
    let mut messages := subgoalPrompt goal.pretty premisesString provider
    unless prompt.isEmpty do messages := messages.push { role := "user", content := prompt }
    let mut session : Option String := none
    let mut error := ""
    for _ in [0:retries] do
      log "prefill" goal.pretty
      log "error" error
      let task ← llm log provider config messages tools constrained session
      llmRef.set (some task)
      let response ← IO.ofExcept task.task.get
      llmRef.set none
      if ← IO.checkCanceled then throwError "canceled."
      messages := messages.push response.message
      session := session <|> response.session
      let some tc := response.message.tool_calls[0]? |
        error := s!"No tool call. Retrying…"
        messages := messages.push { role := "user", content := "You must use the \"have\" tool." }
        continue
      try
        let args : Have ← IO.ofExcept (Json.parse tc.function.arguments >>= fromJson?)
        let type ← elabStringAsExpr args.type
        checkDuplicate mvar type
        let h ← addSubgoal mvar args.name.toName type (args.clear.map (·.toName))
        IO.sleep (stall + start - (← IO.monoMsNow)).toUInt32
        return ⟨mvar, ← getMVarsNoDelayed (← instantiateMVars (.mvar mvar)), h, args.name.toName, type, args.type, messages, tools⟩
      catch e =>
        error ← e.toMessageData.toString
        messages := messages.push { role := "tool", tool_call_id := tc.id, content := error }
    throwError "generate failed."

structure ProviderChoice where
  kind : String := "Local"
  model : String := ""
  prompt : String := ""
deriving ToJson, FromJson

structure ToWidget where
  ctx : CoreMetaContext
  state : CoreMetaState
  expr : WithRpcRef Expr
  empty : WithRpcRef MessageData
  range : Lean.Lsp.Range
  width : Nat
  indent : Nat
  column : Nat
  pipe : WithRpcRef Pipe
  provider : ProviderChoice
deriving RpcEncodable

@[widget_module]
def canonical2Widget : Widget.Module where
  javascript := include_str "include/canonical2.js"

structure ToStep where
  mvar : MVarId
  pipe : WithRpcRef Pipe
  provider : ProviderChoice
deriving RpcEncodable

structure NextGoal where
  mvar : MVarId
  goal : WithRpcRef MessageData
deriving RpcEncodable

@[server_rpc_method]
def nextGoal : WithMeta (WithRpcRef Expr) → RequestM (RequestTask (Option NextGoal)) := asMetaTask fun expr => do
  let goals ← getMVarsNoDelayed (← instantiateMVars expr.val)
  let some currGoal := goals.back? | return none
  let mdc := MessageDataContext.mk (← getEnv) (← getMCtx) (← getLCtx) (← getOptions)
  return some { mvar := currGoal, goal := ← WithRpcRef.mk (MessageData.withContext mdc (MessageData.ofGoal currGoal)) }

@[server_rpc_method]
def step : WithMeta ToStep → RequestM (RequestTask (WithRpcRef MetaTaskUnit)) :=
    asMetaTask fun params => do
  let log := params.pipe.val.log
  let choice := params.provider
  IO.FS.writeFile ((← cacheDir) / "provider.json") (toJson choice).pretty
  let provider ← match choice.kind with
    | "Codex" => pure (.Codex choice.model)
    | "Claude" => pure (.Claude choice.model)
    | _ =>
      startSubgoalDaemon log
      pure (.Llama s!"http://{daemonHost}:{daemonPort}/chat/completions")
  log "print" "Selecting premises…"
  let premises ← select params.mvar { maxSuggestions := 64 } -- TODO uncancelable
  log "print" ""
  let automateTasks := (← automateTasks params.mvar (premises.map (·.name)) 10).map (·.map (fun _ => ()))
  let generateTask := (← generate log params.mvar (premises.map (·.name)) provider
    (wait := 100) (stall := 2000) (prompt := choice.prompt)).map fun _ => ()
  WithRpcRef.mk (← CancelableTask.race (generateTask :: automateTasks))

@[server_rpc_method]
def get (t : WithRpcRef MetaTaskUnit) : RequestM (RequestTask CoreMetaState) := asTask do
  let ((), sCore, sMeta) ← IO.ofExcept (t.val.task.get)
  return { sCore := ← WithRpcRef.mk sCore, sMeta := ← WithRpcRef.mk sMeta }

elab "canonical2" : tactic => do
  let strRange := (← getRef).getRange?.getD (panic! "No range found!")
  let fileMap ← getFileMap
  let range := fileMap.utf8RangeToLspRange strRange
  let width := Lean.Meta.Tactic.TryThis.getInputWidth (← getOptions)
  let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn fileMap strRange

  let copy ← (← getMainGoal).withContext (mkFreshExprMVar (← (← getMainGoal).getType) (userName := `main))
  preprocess copy.mvarId!

  let provider ← try IO.FS.readFile ((← cacheDir) / "provider.json") catch _ => pure ""
  let provider := (Json.parse provider >>= fromJson?).toOption.getD {}

  copy.mvarId!.withContext do
    let toWidget : ToWidget := {
      ctx := {
        ctxCore := ← WithRpcRef.mk (← readThe Core.Context),
        ctxMeta := ← WithRpcRef.mk (← readThe Meta.Context)
      },
      state := {
        sCore := ← WithRpcRef.mk (← getThe Core.State)
        sMeta := ← WithRpcRef.mk (← getThe Meta.State)
      }
      expr := ← WithRpcRef.mk copy,
      empty := ← WithRpcRef.mk ("" : MessageData)
      range := range,
      width := width,
      indent := indent,
      column := column,
      pipe := ← WithRpcRef.mk (← Std.Channel.Sync.new)
      provider
    }

    Lean.Widget.savePanelWidgetInfo (hash canonical2Widget.javascript) (← getRef)
      (props := RpcEncodable.rpcEncode toWidget)

    let goal ← getMainGoal
    goal.admit
