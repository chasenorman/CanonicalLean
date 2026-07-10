module

import Lean
public import Canonical.Destruct.Util
open Lean Core Meta

-- Potentially
-- abbrev DestructM := ReaderT (TreeMap Name Isomorphism) MetaM

public section

inductive DestructInfo where
  | trivial
  | induct (builtinCtors : Array Expr) (builtinRec : Level → Expr)
  | pi (inputTypes : Array Expr) (outputType : Expr)
  deriving Inhabited

structure Isomorphism where
  t : Expr
  constructors : Array Expr
  recursor : Expr

def extractInfo (t : Expr) : MetaM (Option DestructInfo) := do
  if !(← inferType t).isSort then return .none
  let t' ← whnf t
  match t' with
  | .const _ _
  | .app _ _ => do
    let headName := t'.getAppFn.constName!
    let headLevels := t'.getAppFn.constLevels!
    let headArgs := t'.getAppArgs
    if !(← isInductive headName) then return .none
    let inductInfo ← getConstInfoInduct headName
    if inductInfo.isRec || inductInfo.isReflexive then
      return .some $ DestructInfo.trivial
    let ctorNames := inductInfo.ctors.toArray
    let recName := headName ++ `rec
    return DestructInfo.induct
      (ctorNames.map fun name => mkAppN (Expr.const name headLevels) headArgs)
      (fun motiveLevel => mkAppN (Expr.const recName (motiveLevel::headLevels)) headArgs)
  | .forallE _ _ _ _ =>
    forallTelescope t fun inputVars outputType => do
      let inputTypes ← inputVars.mapM inferType
      return .some $ DestructInfo.pi inputTypes outputType
  | _ =>
    return .some DestructInfo.trivial

def destructTrivial (t : Expr) : MetaM (Option Isomorphism) := do
  let ctor := Expr.lam `x t (Expr.bvar 0) .default
  let recursor ← withRecursor t #[ctor] fun _X ctors input => do
    return Expr.app ctors[0]! input
  return .some {
    t := t,
    constructors := #[ctor],
    recursor := recursor
  }

mutual
partial def destructInduct (t : Expr) (builtinCtors : Array Expr) (builtinRec : Level → Expr) : MetaM (Option Isomorphism) := do
  return .none

partial def destructPi (t : Expr) (inputTypes : Array Expr) (outputType : Expr) : MetaM (Option Isomorphism) := do
  return .none

partial def destruct (t : Expr) : MetaM (Option Isomorphism) := do
  if !(← inferType t).isSort then return .none
  let t ← whnf t
  let optInfo ← extractInfo t
  if optInfo.isNone then return .none

  match optInfo.get! with
  | .trivial => do
    destructTrivial t
  | .induct builtinCtors builtinRec => do
    destructInduct t builtinCtors builtinRec
  | .pi inputTypes outputType => destructPi t inputTypes outputType
end

end
