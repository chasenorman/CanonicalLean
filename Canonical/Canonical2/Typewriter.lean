module

public meta import Canonical.Canonical2.Basic
public import Canonical.Canonical2.Rpc
public import Lean.LibrarySuggestions.Basic
public import Lean.Expr
public import Lean.Server.Rpc.Basic
public import Lean.Message

open Lean Meta Expr Elab Term Server Tactic Core RequestM IO LibrarySuggestions

public meta section

namespace Canonical2

instance : TypeName (IO.Process.Child ⟨IO.Process.Stdio.null, IO.Process.Stdio.piped, IO.Process.Stdio.inherit⟩) := unsafe (.mk _ ``IO.Process.Child)

structure MVarData where
  mvarId : MVarId
  name : String
  messageData : WithRpcRef MessageData
deriving RpcEncodable

structure Save where
  state : CoreMetaState
  selected : Nat
  mvars : Array MVarData
deriving RpcEncodable

structure ToTypewriter where
  ctx : CoreMetaContext
  key : String
  token : String
  initial : Save
  expr : WithRpcRef Expr
  empty : WithRpcRef MessageData
  range : Lean.Lsp.Range
  width : Nat
  indent : Nat
  column : Nat
deriving RpcEncodable

@[widget_module]
def typewriterWidget : Widget.Module where
  javascript := (include_str "include/unicode-input-component.js") ++ "\n" ++ (include_str "include/typewriter.js")

def getMVarData (expr : Expr) : MetaM (Array MVarData) := do
  (← getMVarsNoDelayed expr).mapM fun (mvarId : MVarId) => do
    let mdecl ← mvarId.getDecl
    let mdc := MessageDataContext.mk (← getEnv) (← getMCtx) (← getLCtx) (← getOptions)
    return {
      mvarId := mvarId,
      name := mdecl.userName.toString,
      messageData := ← WithRpcRef.mk (MessageData.withContext mdc (MessageData.ofGoal mvarId))
    }

structure ToAddSubgoal where
  mvarId : MVarId
  name : String
  type : String
  clears : String

  selected : Nat
  expr : WithRpcRef Expr
deriving RpcEncodable

inductive FromAddSubgoal where
| success (result : Save)
| error (msg : WithRpcRef MessageData)
deriving RpcEncodable

def mkSave (selected : Nat) (expr : Expr) : MetaM Save := do
  let mvars ← getMVarData expr
  return {
    state := {
      sCore := ← WithRpcRef.mk (← getThe Core.State),
      sMeta := ← WithRpcRef.mk (← getThe Meta.State)
    },
    selected, mvars
  }

@[server_rpc_method]
def addSubgoalRpc : WithMeta ToAddSubgoal → RequestM (RequestTask FromAddSubgoal) :=
  asMetaTask fun (params : ToAddSubgoal) => do
    try params.mvarId.withContext do
      let typeExpr ← TermElabM.run' do elabStringAsExpr params.type
      let clears := ((params.clears.splitToList (fun c => c.isWhitespace || c == ',')).filter (fun s => !s.isEmpty)).map fun s => s.toName
      let _ ← addSubgoal params.mvarId params.name.toName typeExpr clears.toArray
      return .success (← mkSave params.selected params.expr.val)
    catch e => return .error (← WithRpcRef.mk e.toMessageData)

structure ToOverride where
  mvarId : MVarId
  term : String

  selected : Nat
  expr : WithRpcRef Expr
deriving RpcEncodable

@[server_rpc_method]
def overrideRpc : WithMeta ToOverride → RequestM (RequestTask FromAddSubgoal) :=
  asMetaTask fun (params : ToOverride) => do
    try params.mvarId.withContext do
      let type ← params.mvarId.getType
      let stx ← IO.ofExcept (Parser.runParserCategory (← getEnv) `term params.term)
      let proof ← elabStringAsExpr params.term (type := type)
      params.mvarId.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax stx)) proof)
      return .success (← mkSave params.selected params.expr.val)
    catch e => return .error (← WithRpcRef.mk e.toMessageData)

@[server_rpc_method]
def automateRpc : WithMeta MVarId → RequestM (RequestTask (WithRpcRef (MetaTask Unit))) := asMetaTask fun mvarId => do
  let premises ← select mvarId { maxSuggestions := 64 }
  WithRpcRef.mk (← automate mvarId (premises.map (·.name)))

deriving instance RpcEncodable for Option

structure ToTaskGet where
  task: WithRpcRef MetaTaskUnit
  ctx: CoreMetaContext

  selected : Nat
  expr : WithRpcRef Expr
deriving RpcEncodable

@[server_rpc_method]
def taskGet (params : ToTaskGet) : RequestM (RequestTask (Option Save)) := asTask do
  match params.task.val.task.get with
  | Except.error _ => return .none
  | Except.ok ((), sCore, sMeta) =>
    CoreM.run' (ctx := params.ctx.ctxCore.val) (s := sCore) do
      MetaM.run' (ctx := params.ctx.ctxMeta.val) (s := sMeta) do
        return .some (← mkSave params.selected params.expr.val)

elab "typewriter" : tactic => do
  let strRange := (← getRef).getRange?.getD (panic! "No range found!")
  let fileMap ← getFileMap
  let range := fileMap.utf8RangeToLspRange strRange
  let width := TryThis.getInputWidth (← getOptions)
  let (indent, column) := TryThis.getIndentAndColumn fileMap strRange

  let copy ← (← getMainGoal).withContext (mkFreshExprMVar (← (← getMainGoal).getType) (userName := `main))
  preprocess copy.mvarId!

  let token := toString (← IO.monoNanosNow)
  let toTypewriter : ToTypewriter := {
    ctx := {
      ctxCore := ← WithRpcRef.mk (← readThe Core.Context),
      ctxMeta := ← WithRpcRef.mk (← readThe Meta.Context)
    },
    key := token,
    token := token,
    initial := ← mkSave 0 copy,
    expr := ← WithRpcRef.mk copy,
    empty := ← WithRpcRef.mk ("" : MessageData)
    range := range,
    width := width,
    indent := indent,
    column := column
  }

  Widget.savePanelWidgetInfo typewriterWidget.javascriptHash (← getRef)
    (props := rpcEncode toTypewriter)

  let goal ← getMainGoal
  goal.admit
