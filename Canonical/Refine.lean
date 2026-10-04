module

public meta import Canonical.FromCanonical
public import Lean.Meta.Tactic.TryThis
public import Canonical.Util

namespace Canonical

public meta section

open Lean Elab Meta Tactic Server RequestM

/-- Data shared between the tactic process and RPC process. -/
structure RpcData where
  config: Config
  processedGoal: MVarId
  mctx: MetavarContext
  mainGoal: MVarId
  reconstruct: Lean.Expr → MetaM Lean.Expr
  width: Nat
  indent: Nat
  column: Nat
deriving TypeName

structure InsertParams where
  rpcData : Server.WithRpcRef RpcData
  /-- Position of our widget instance in the Lean file. -/
  pos : Lsp.Position
  range: Lsp.Range
deriving Server.RpcEncodable

/-- Obtains the current term from the refinement UI. -/
@[never_extract, extern "get_refinement"] opaque getRefinement : IO Canonical.Expr

/-- Gets the String to be inserted into the document, for the refinement widget. -/
@[server_rpc_method]
def getRefinementStr (params : InsertParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do runTermElabM snap do
    let data := params.rpcData.val
    withMCtx data.mctx do withArityUnfold data.config.monomorphize do withOptions applyOptions do
      let expr ← data.processedGoal.withContext do
        data.reconstruct (← fromCanonical (← getRefinement) (← data.processedGoal.getType))

      data.mainGoal.withContext do leanString expr true

/-- The widget for the refinement UI. -/
@[widget_module]
def refineWidget : Widget.Module where
  javascript := include_str "../refine.js"
