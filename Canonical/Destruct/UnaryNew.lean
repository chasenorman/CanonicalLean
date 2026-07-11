module

import Lean
public import Canonical.Util
public import Canonical.Destruct.Util
open Lean Core Meta

-- Potentially
-- abbrev DestructM := ReaderT (TreeMap Name Isomorphism) MetaM

public section

structure Isomorphism where
  t : Expr
  constructors : Array Expr
  recursor : Expr
  deriving Inhabited

def destructTrivial (t : Expr) : MetaM (Option Isomorphism) := do
  let ctor := Expr.lam `x t (Expr.bvar 0) .default
  let recursor ← withRecursor t #[ctor] fun _ X ctors input => do
    return Expr.app ctors[0]! input
  return .some {
    t := t,
    constructors := #[ctor],
    recursor := recursor
  }

mutual
partial def destructCtor (t : Expr) (ctor : Expr) : MetaM (Option (Array Isomorphism)) := do
  let optIsos ← constructorTelescope (← inferType ctor) t fun fvars => do
    fvars.mapM fun input => do destruct (← inferType input)
  return optIsos.mapM id


partial def destructInduct (t : Expr) (builtinCtors : Array Expr) (builtinRec : Level → Expr) : MetaM (Option Isomorphism) := do
  let .some isoBlocks := (← builtinCtors.mapM (destructCtor t ·)).mapM id | return .none
  let ctorBlocks ← builtinCtors.mapIdxM fun i builtinCtor => do
    let allCtors := isoBlocks[i]!.map (·.constructors)
    let isoTypes := isoBlocks[i]!.map (·.t)
    withCartesianProductM allCtors fun ctorChoices => do
      let ctorTypes ← ctorChoices.mapM inferType
      let factorSizes := (isoTypes.zip ctorTypes).map fun (isoType, ctorType) => constructorArity ctorType isoType
      constructorTelescopeN ctorTypes isoTypes fun allInputs => do
        let packedInputs := repackage allInputs factorSizes
        let builtinArgs := (ctorChoices.zip packedInputs).map fun (ctor, inputs) =>
          Canonical.apply ctor inputs.toList
        mkLambdaFVars allInputs (mkAppN builtinCtor builtinArgs)
  let constructors := ctorBlocks.flatten
  let recursor ← withRecursor t constructors fun level X ctors input => do
    let builtinMotive := Expr.lam `_ t X .default
    let recBranches := #[] -- TODO
    return mkAppN (builtinRec level) (#[builtinMotive] ++ recBranches ++ #[input])
  return .some {
    t := t,
    constructors := constructors,
    recursor := recursor
  }

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

#eval (do
  let e := toExpr ((Option.none, Option.none, Option.none, Option.none) : Option Nat × Option Nat × Option Nat × Option Nat)
  let t ← inferType e
  IO.println $ ← (← destruct t).get!.constructors.mapM ppExpr
  )

end
