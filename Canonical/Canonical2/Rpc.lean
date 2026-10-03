module

public meta import Lean.Meta.Tactic.TryThis
public import Lean.Meta.Basic
public import Lean.Server.Requests
public import Lean.Server.Rpc.RequestHandling
public meta import Canonical.Canonical2.Util
public meta import Canonical.Symbols
public meta import Canonical.Util
public meta import Std.Sync.Channel
import Canonical.Canonical2.Basic

open Lean Meta Expr Elab Term Server Tactic Core RequestM IO

namespace Canonical2

public meta section

instance : TypeName Core.Context := unsafe (.mk _ ``Core.Context)
instance : TypeName Core.State := unsafe (.mk _ ``Core.State)
instance : TypeName Meta.Context := unsafe (.mk _ ``Meta.Context)
instance : TypeName Meta.State := unsafe (.mk _ ``Meta.State)
instance : TypeName Expr := unsafe (.mk _ ``Expr)
instance : TypeName MessageData := unsafe (.mk _ ``MessageData)
abbrev MetaTaskUnit := MetaTask Unit
instance : TypeName MetaTaskUnit := unsafe (.mk _ ``MetaTaskUnit)
abbrev Pipe := Std.Channel.Sync Json
instance : TypeName Pipe := unsafe (.mk _ ``Pipe)

deriving instance RpcEncodable for PUnit

structure CoreMetaState where
  sCore : WithRpcRef Core.State
  sMeta : WithRpcRef Meta.State
deriving RpcEncodable

structure CoreMetaContext where
  ctxCore : WithRpcRef Core.Context
  ctxMeta : WithRpcRef Meta.Context
deriving RpcEncodable

structure WithMeta (α : Type) where
  ctx : CoreMetaContext
  state : CoreMetaState
  val : α
deriving RpcEncodable

def asMetaTask {α β : Type} (f : α → MetaM β) : WithMeta α → RequestM (RequestTask β) := fun x => asTask do
  CoreM.run' (ctx := x.ctx.ctxCore.val) (s := x.state.sCore.val) do
    MetaM.run' (ctx := x.ctx.ctxMeta.val) (s := x.state.sMeta.val) do
      f x.val

structure ToLeanString where
  expr : WithRpcRef Expr
  width : Nat
  indent : Nat
  column : Nat
  exact : Bool
deriving RpcEncodable

def removeUnusedHaves (e : Expr) : MetaM Expr := do
  Meta.transform (← instantiateMVars e) (post := fun e => return .done (consumeUnusedLet e (consumeNondep := true)))

@[server_rpc_method]
def leanStringRpc : WithMeta ToLeanString → RequestM (RequestTask String) := asMetaTask fun params => do
  let expr ← instantiateMVars params.expr.val
  let mvars ← getMVarsNoDelayed expr
  -- This is necessary for two reasons:
  -- 1. Delayed assigned metavariables are not printed unless the assignment contains no metavariables.
  --    (Note that getMVars does not recursively collect delayed assigned metavariables)
  -- 2. The widget expects metavariables to be represented by name, not userName.
  mvars.forM fun mvarId => mvarId.withContext do
    mvarId.checkNotAssigned `admit
    let decl := (← getMCtx).getDecl mvarId
    let mvarType := decl.type
    let ident := mkIdent mvarId.name
    let stx := if params.exact then `(syntheticHole| ?_) else `(syntheticHole| ?$ident)
    let val ← mkLabeledSorry mvarType true (unique := true)
    mvarId.assign (.mdata (KVMap.empty.insert `canonical (.ofSyntax (Unhygienic.run stx))) val)

  Canonical.leanString (← if mvars.isEmpty then do removeUnusedHaves expr else pure expr) params.exact
    params.width params.indent params.column

@[server_rpc_method]
def cancel (task : WithRpcRef MetaTaskUnit) : RequestM (RequestTask Unit) :=
  asTask task.val.cancel

def Pipe.log (pipe : Pipe) (key value : String) : IO Unit :=
  pipe.send (Json.mkObj [(key, Json.str value)])

@[server_rpc_method]
def recv (pipe : WithRpcRef Pipe) : RequestM (RequestTask Json) := asTask pipe.val.recv
