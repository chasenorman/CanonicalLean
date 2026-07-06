module

import Lean

open Lean Core Meta

structure Isomorphism where
  constructors : Array Expr
  recursor : Expr
  deriving Inhabited, Repr

def forallTelescopeN
  (types : List Expr)
  (k : List (Array Expr) → List Expr → MetaM α) :
  MetaM α :=
    match types with
    | [] => k [] []
    | t::types' => forallTelescope t fun inputFVars outputType =>
      forallTelescopeN types' fun inputs outputs => k (inputFVars::inputs) (outputType::outputs)

def recursify (forallType : Expr) (newOutputType : Expr) : MetaM Expr := do
  forallTelescope forallType fun fvars _ =>
    mkForallFVars fvars newOutputType

inductive DestructInfo where
  | trivial
  | induct (builtinCtors : Array Expr) (builtinRec : Expr)
  | pi (inputType : Expr) (outputType : Expr)
  deriving Inhabited, Repr

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
      (mkAppN (Expr.const recName headLevels) headArgs)
  | .forallE _ inputType outputType _ =>
    return .some $ DestructInfo.pi inputType outputType
  | _ =>
    return .some DestructInfo.trivial

def withDNFProductM (factors : Array Isomorphism) (k : Array Expr → MetaM α) : MetaM (Array α) := do
  let dnfSize := (factors.map (·.constructors.size)).prod
  let mut combinations : Array α := Array.emptyWithCapacity dnfSize
  for i in [:dnfSize] do
    let mut indices := Array.emptyWithCapacity factors.size
    let mut j := i
    for k in [:factors.size] do
      indices := indices.push (j % factors[k]!.constructors.size)
      j := j / factors[k]!.constructors.size
    combinations := combinations.push
      (← k (indices.mapIdx fun k idx => factors[k]!.constructors[idx]!))
  return combinations

def destructTrivial (t : Expr) : MetaM (Option Isomorphism) := do
  let ctorTrivial :=
    Expr.lam `x t (Expr.bvar 0) .default
  let recTrivial ←
    withLocalDecl `X .default (Expr.sort (← Meta.mkFreshLevelMVar)) fun fvarX => do
      withLocalDecl `f .default (Expr.forallE .anonymous t fvarX .default) fun fvarF => do
        withLocalDecl `x .default t fun fvarInput => do
          return ← mkLambdaFVars #[fvarX, fvarF, fvarInput] (Expr.app fvarF fvarInput)
  return .some {
    constructors := #[ctorTrivial],
    recursor := recTrivial
  }

mutual
partial def destructInduct (t : Expr) (builtinCtors : Array Expr) (builtinRec : Expr) : MetaM (Option Isomorphism) := do
  let constructors : Option (Array (Array Expr)) := Array.mapM (f := id)
    (← builtinCtors.mapM fun builtinCtor => do
    forallTelescope (← inferType builtinCtor) fun inputVars _ => do
      let isos := (← (← inputVars.mapM inferType).mapM destruct).mapM id
      if isos.isNone then return .none
      return .some $ ← withDNFProductM isos.get! fun ctors => do
        forallTelescopeN (← ctors.mapM inferType).toList fun destructed _ => do
          let destructed := destructed.toArray
          let allVars := destructed.flatten
          let args := destructed.mapIdx fun i vars => mkAppN ctors[i]! vars
          mkLambdaFVars allVars $ mkAppN builtinCtor args)
  if constructors.isNone then return .none
  return .some {
    constructors := constructors.get!.flatten,
    recursor := Inhabited.default
  }

partial def destructPi (t : Expr) (inputType : Expr) (outputType : Expr) : MetaM (Option Isomorphism) := do
  return .none

partial def destruct (t : Expr) : MetaM (Option Isomorphism) := do
  if !(← inferType t).isSort then return .none
  let t ← whnf t
  let optInfo ← extractInfo t
  if optInfo.isNone then return .none

  match optInfo.get! with
  | .trivial => destructTrivial t
  | .induct builtinCtors builtinRec => destructInduct t builtinCtors builtinRec
  | .pi inputType outputType => destructPi t inputType outputType
end

#eval show MetaM Unit from (do
  let t ← inferType (toExpr (2, 3))
  IO.println $ (← destruct t).get!.constructors
  )
