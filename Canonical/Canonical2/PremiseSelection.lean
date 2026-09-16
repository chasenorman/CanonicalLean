module

public meta import Std.Sync.Channel
public meta import Lean.LibrarySuggestions.Basic
public meta import Canonical.Canonical2.Llama
public import Canonical.Canonical2.Rpc

open Lean Meta System Elab Tactic Server RequestM LibrarySuggestions

namespace Canonical2

public meta section

deriving instance FromJson for Suggestion

run_cmd
  for module in #[
    "Aesop", "Auto", "Cli", "CodeAction", "cvc5", "DocGen4", "Duper", "Hammer", "ImportGraph", "Lake", "Lean",
    "LeanSearchClient", "Linter", "Mathport", "MD4Lean", "Plausible", "ProofWidgets", "Qq", "QuerySMT", "Smt",
    "Tactic", "TacticExtra", "Test", "Testing", "UnicodeBasic", "Util", "Canonical"
  ] do
    modifyEnv fun env => moduleDenyListExt.addEntry env module

run_cmd
  for name in #["Lean", "Lake", "Qq"] do
    modifyEnv fun env => nameDenyListExt.addEntry env name

private structure Premise where
  name: Name
  decl: String
deriving ToJson

private def getModuleVersionToken (mod : Name) : IO String := do
  let path ← findOLean mod
  let hash ← Lake.Hash.load? (FilePath.mk <| path.toString ++ ".hash")
  return (← hash.getDM (Lake.computeBinFileHash path)).hex

private def curlPost (path : String) (data : Json) : IO String := do
  let url := s!"http://{daemonHost}:{premisePort}{path}"
  let out ← IO.Process.output {
    cmd := "curl"
    args := #["-sS", "-X", "POST", "--header", "Content-Type: application/json", "--data", "@-", url]
  } (some data.compress)
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"curl to {url} failed:\n{out.stderr}"
  return out.stdout

private def request {α} [FromJson α] (path : String) (data : Json) : IO α := do
  IO.ofExcept (Json.parse (← curlPost path data) >>= fromJson?)

private def getCachedModuleVersionTokens (mods : Array Name) : IO (Array (Option String)) :=
  request "/version" (Json.mkObj [("modules", toJson (mods.map (·.toString)))])

private def cacheModule (mod : Name) (declarations : Array Premise) (token : String) : IO Unit := do
  let _ ← curlPost "/cache" (Json.mkObj [
    ("module", toJson mod.toString),
    ("declarations", toJson declarations),
    ("token", toJson token)])

private def selectPremises (modules : Array Name) (declarations : Array Premise)
    (goal : String) (k : Nat) : IO (Array Suggestion) :=
  request "/select" (Json.mkObj [
    ("modules", toJson (modules.map (·.toString))),
    ("declarations", toJson declarations),
    ("goal", toJson goal),
    ("k", toJson k)])

private def getKind (cinfo : ConstantInfo) : MetaM String := do
  let env ← getEnv
  return match cinfo with
    | .axiomInfo _  => "axiom"
    | .thmInfo _    => "theorem"
    | .opaqueInfo _ => "opaque"
    | .defnInfo i   => if isInstanceCore env i.name then "instance" else "def"
    | .inductInfo i =>
      if isClass env i.name then "class"
      else if isStructure env i.name then "structure"
      else "inductive"
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => "def"

private def toPremise (name : Name) : MetaM (Option Premise) := do
  if isDeniedPremise (← getEnv) name then return none
  withCurrHeartbeats do try
    let kind ← getKind (← getConstInfo name)
    let ⟨fmt, _⟩ ← PrettyPrinter.ppSignature name
    let docPrefix := match ← findSimpleDocString? (← getEnv) name with
      | some doc => "/-- " ++ doc.dropSuffix " " ++ " -/\n"
      | none => ""
    return some ⟨name, docPrefix ++ kind ++ " " ++ fmt.pretty 1000000000⟩
  catch _ => return none

private def select (log : String → String → IO Unit) (goal : MVarId) (config : LibrarySuggestions.Config) :
    MetaM (Array Suggestion) := withOptions roundtrip do
  startPremiseDaemon log (prebuilt := false)
  let env ← getEnv
  let mods := env.allImportedModuleNames.filter (!isDeniedModule env ·)
  let cached ← getCachedModuleVersionTokens mods
  let tokens ← mods.mapM (getModuleVersionToken ·)
  let stale := (mods.zip (cached.zip tokens)).filterMap fun (mod, cached, token) =>
    if cached == token then none else some (mod, token)
  for h : i in [:stale.size] do
    let (mod, token) := stale[i]
    log "status" s!"Embedding {mod} ({i + 1}/{stale.size}):"
    log "progress" (toString (100 * i / stale.size))
    let decls := env.header.moduleData[(env.getModuleIdx? mod).get!]!.constNames
    cacheModule mod (← decls.filterMapM toPremise) token
  unless stale.isEmpty do
    log "progress" ""
  log "status" "Selecting premises…"
  let decls := env.constants.foldStage2 (fun _ => ·.push ·) #[]
  let premises ← decls.filterMapM toPremise
  let goal ← Meta.ppGoal goal
  let suggestions ← selectPremises mods premises goal.pretty config.maxSuggestions
  log "status" ""
  suggestions.filterM (config.filter ·.name)

@[library_suggestions] def premiseSelector : Selector := fun goal config =>
  select (fun _ _ => pure ()) goal config

structure WidgetSuggestion where
  score : Float
  decl : WithRpcRef MessageData
deriving RpcEncodable

abbrev SuggestTask := Task (Except IO.Error (Array WidgetSuggestion))

instance : TypeName SuggestTask := unsafe (.mk _ ``SuggestTask)

structure SuggestProps where
  task : WithRpcRef SuggestTask
  pipe : WithRpcRef Pipe
deriving RpcEncodable

private def widgetSuggestions (log : String → String → IO Unit) (goal : MVarId) (k : Nat) :
    MetaM (Array WidgetSuggestion) := do
  let mdc := MessageDataContext.mk (← getEnv) (← getMCtx) (← getLCtx) (← getOptions)
  (← select log goal { maxSuggestions := k }).mapM fun s => return {
    score := s.score, decl := ← WithRpcRef.mk (MessageData.withContext mdc (.ofConstName s.name)) }

@[server_rpc_method]
def getSuggestions (task : WithRpcRef SuggestTask) : RequestM (RequestTask (Array WidgetSuggestion)) :=
  asTask (IO.ofExcept task.val.get)

@[widget_module]
def suggestWidget : Widget.Module where
  javascript := include_str "include/suggest.js"

/-- Select relevant constants from the imported library modules. -/
syntax (name := suggestTac) "suggest" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| suggest $[$k?]?) => do
    let k := (k?.map (·.getNat)).getD 20
    let pipe : Pipe ← Std.Channel.Sync.new
    let goal ← getMainGoal
    let task ← goal.withContext (widgetSuggestions pipe.log goal k).toTask
    let props : SuggestProps := {
      task := ← WithRpcRef.mk (task.task.map (sync := true) (·.map (·.1)))
      pipe := ← WithRpcRef.mk pipe
    }
    Widget.savePanelWidgetInfo (hash suggestWidget.javascript) (← getRef)
      (props := RpcEncodable.rpcEncode props)
    goal.admit
    Lean.logInfoAt (← getRef) ""
