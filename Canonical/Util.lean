import Lean

open Lean Meta Expr Name

namespace Canonical

structure Arity where
  params : Array Arity := #[]
deriving Inhabited

partial def arityToString (arity : Arity) : String :=
  toString (arity.params.map (fun params => s!"({arityToString params})"))
instance : ToString Arity where toString := arityToString

partial def typeArity (e : Expr) : MetaM Arity := do
  forallTelescopeReducing e fun xs _ => do
    pure ⟨← xs.mapM fun param => do
      let id := param.fvarId!
      pure (← typeArity (← id.getType))⟩

partial def typeArity1 (e : Expr) : MetaM Nat := do
  forallTelescopeReducing e fun xs _ => return xs.size

def toHead : Expr → MetaM (Name × Expr)
| fvar id =>
  return (id.name.updatePrefix (← id.getUserName).getRoot, ← id.getType)
| mvar id =>
  return (((← getMCtx).getDecl id).userName, ← id.getType)
| sort l =>
  return (`Sort, .sort (l.succ))
| const name us =>
  return (name, (← getConstInfo name).instantiateTypeLevelParams us)
| lit l =>
  let name : Name := match l with
  | .natVal n => .num .anonymous n
  | .strVal s => .str .anonymous s!"\"{s}\""
  return (name, l.type)
| _ => unreachable!

def toNameString (e : Expr) : MetaM String := return (← toHead e).1.toString

partial def hidesForall (e : Expr) : MetaM Bool := do
  match ← whnf e with
  | .lam name type body info =>
    withLocalDecl name info type fun fvar => hidesForall (body.instantiate1 fvar)
  | .forallE _ _ _ _ => pure true
  | _ => pure false

def canUnfold (monomorphize : Bool) (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | .all => return true
  | .default => return !(← isIrreducible info.name)
  | m =>
    if (← isReducible info.name) then
      return true
    else if m == .instances && isGlobalInstance (← getEnv) info.name &&
      (!monomorphize || (← (isClass? (info.type)).run' {}) == some `OfNat) then
      return true
    else if let some value := info.value? then
      return ← (hidesForall value).run' {}
    else return false

def isRecursive (e : Expr) : MetaM Bool := do
  let env ← getEnv
  return e.getUsedConstants.any fun c =>
    (env.find? c).get! matches .recInfo _ || isAuxRecursor env c

def rawRawNatLit : Nat → Expr
| 0 => .const ``Nat.zero []
| n + 1 => .app (.const ``Nat.succ []) (rawRawNatLit n)

variable [MonadControlT MetaM n] [Monad n]
@[inline] def withArityUnfold (monomorphize : Bool) (e : n α) : n α :=
  withReducibleAndInstances (withCanUnfoldPred (canUnfold monomorphize) e)

def printForce (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush

def applyOptions : Options → Options :=
  (pp.proofs.set · true |>
  (pp.motives.all.set · true |>
  (pp.coercions.set · false |>
  (pp.unicode.fun.set · true))))
