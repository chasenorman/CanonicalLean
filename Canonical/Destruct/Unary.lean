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

-- Like regular withLocalDecls but one can control package together the free
-- variables and dependencies between arguments are removed for simplicity
def withLocalDeclsDN [Inhabited α] (typeBlocks : List (Array Expr)) (k : List (Array Expr) → MetaM α) : MetaM α :=
  match typeBlocks with
  | [] => k []
  | types::typeBlocks' => do
    withLocalDeclsD
      (← types.mapM fun t => do pure (← mkFreshId, fun _ => pure t)) fun fvars => do
      withLocalDeclsDN typeBlocks' fun fvarsBlocks => k (fvars::fvarsBlocks)

def recursify (forallType : Expr) (newOutputType : Expr) : MetaM Expr := do
  forallTelescope forallType fun fvars _ =>
    mkForallFVars fvars newOutputType

inductive DestructInfo where
  | trivial
  | induct (builtinCtors : Array Expr) (builtinRec : Level → Expr)
  | pi (inputType : Expr) (outputType : Expr)
  deriving Inhabited

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
  | .forallE _ inputType outputType _ =>
    return .some $ DestructInfo.pi inputType outputType
  | _ =>
    return .some DestructInfo.trivial

def withDNFProductM [Monad n] (factors : Array Isomorphism) (k : Array Expr → n α) : n (Array α) := do
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

partial def mkProductRecursor (X : Expr) (isos : Array Isomorphism) (fields : Array Expr) (ctors : Array Expr) : MetaM Expr := do
  let rec loop (level : Nat) (ctorIdx : Nat) (vars : Array Expr) : MetaM Expr := do
    if level == isos.size then return mkAppN ctors[ctorIdx]! vars
    let idxStep := isos[level]!.constructors.size
    let recHead := Expr.app isos[level]!.recursor X
    let recCases ← isos[level]!.constructors.mapIdxM fun i ctor => do
      forallTelescope (← inferType ctor) fun inputVars _ => do
        mkLambdaFVars inputVars $ ← loop (level + 1) (idxStep * ctorIdx + i) (vars ++ inputVars)
    return mkAppN recHead (recCases ++ #[fields[level]!])
  loop 0 0 #[]

def destructTrivial (t : Expr) : MetaM (Option Isomorphism) := do
  let ctor :=
    Expr.lam `x t (Expr.bvar 0) .default
  let recursor ←
    withLocalDeclD `X (Expr.sort (← Meta.mkFreshLevelMVar)) fun fvarX => do
      withLocalDeclD `f (Expr.forallE .anonymous t fvarX .default) fun fvarF => do
        withLocalDeclD `x t fun fvarInput => do
          return ← mkLambdaFVars #[fvarX, fvarF, fvarInput] (Expr.app fvarF fvarInput)
  return .some {
    constructors := #[ctor],
    recursor := recursor
  }

mutual
partial def destructInduct (t : Expr) (builtinCtors : Array Expr) (builtinRec : Level → Expr) : MetaM (Option Isomorphism) := do
  let isomorphisms : Option (Array (Array Isomorphism)) := Array.mapM (f := id)
    (← builtinCtors.mapM fun builtinCtor => do
      forallTelescope (← inferType builtinCtor) fun inputVars _ => do
        return (← inputVars.mapM fun var => do destruct (← inferType var)).mapM id)
  if isomorphisms.isNone then return .none
  let isomorphisms := isomorphisms.get!
  let constructorCases : Array (Array Expr) ← isomorphisms.mapIdxM fun i isos => do
    let builtinCtor := builtinCtors[i]!
    withDNFProductM isos fun ctors => do
      forallTelescopeN (← ctors.mapM inferType).toList fun destructedArgs _ => do
        let destructedArgs := destructedArgs.toArray
        let builtinArgs := destructedArgs.mapIdx fun k args => mkAppN ctors[k]! args
        mkLambdaFVars destructedArgs.flatten $ mkAppN builtinCtor builtinArgs
  let constructors := constructorCases.flatten
  -- Perhaps we can pass the motiveLevel down to further recursive calls?
  let motiveLevel ← Meta.mkFreshLevelMVar
  let recursor ←
    withLocalDeclD `X (Expr.sort motiveLevel) fun fvarX => do
      let constructorTypes ← constructorCases.mapM (·.mapM fun ctor => do recursify (← inferType ctor) fvarX)
      withLocalDeclsDN constructorTypes.toList fun fvarCtorBlocks => do
        let fvarCtorBlocks := fvarCtorBlocks.toArray
        withLocalDecl `x .default t fun fvarInput => do
          let recHead := Expr.app (builtinRec motiveLevel) (Expr.lam `_ t fvarX .default)
          let recCases ← isomorphisms.mapIdxM fun i isos => do
            forallTelescope (← inferType builtinCtors[i]!) fun inputVars _ => do
              mkLambdaFVars inputVars $ ← mkProductRecursor fvarX isos inputVars fvarCtorBlocks[i]!
          mkLambdaFVars
            (#[fvarX] ++ fvarCtorBlocks.flatten ++ #[fvarInput])
            (mkAppN recHead (recCases ++ #[fvarInput]))
  return .some {
    constructors := constructors,
    recursor := recursor
  }

partial def destructPi (t : Expr) (inputType : Expr) (outputType : Expr) : MetaM (Option Isomorphism) := do
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
  | .pi inputType outputType => destructPi t inputType outputType
end

#eval show MetaM Unit from (do
  let t ← inferType (toExpr ((Option.some 2, []) : Option Nat × List Nat))
  let iso := (← destruct t).get!
  for constructor in iso.constructors do
    IO.println $ ← betaReduce constructor
  IO.println ""
  IO.println $ iso.recursor
  IO.println ""
  IO.println $ ← betaReduce iso.recursor
  IO.println ""
  IO.println $ ← check (← betaReduce iso.recursor)
  )
