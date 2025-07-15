import Lean
import Canonical.FromCanonical

namespace Canonical

open Lean Elab Meta Tactic
structure RpcData where
  goal: Expr
  lctx: LocalContext
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
@[never_extract, extern "get_refinement"] opaque getRefinement : IO Term

open Server RequestM in
/-- Gets the String to be inserted into the document, for the refinement widget. -/
@[server_rpc_method]
def getRefinementStr (params : InsertParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do runTermElabM snap do
    let data := params.rpcData.val
    withLCtx' data.lctx do withArityUnfold do withOptions applyOptions do
      let expr ← fromCanonical (← getRefinement) data.goal
      let tm ← Lean.Meta.Tactic.TryThis.delabToRefinableSyntax expr
      let stx ← `(tactic| refine $tm)
      let fmt ← Lean.PrettyPrinter.ppCategory `tactic stx
      let str := Std.Format.pretty fmt data.width data.indent data.column
      pure str

/-- The widget for the refinement UI. -/
@[widget_module]
def refineWidget : Widget.Module where
  javascript := include_str "../refine.js"
