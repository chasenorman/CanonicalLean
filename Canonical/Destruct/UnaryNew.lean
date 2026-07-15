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

/-- Returns an expression of nested recursor calls that recurse on `values` in
    sequence, executing `k` on all possible branching cases. -/
partial def withRecurseOn (X : Expr) (values : Array Expr) (isos : Array Isomorphism) (k : Array Nat → Array Expr → MetaM Expr) : MetaM Expr := do
  let rec loop (valueIdx : Nat) (ctorIndices : Array Nat) (vars : Array Expr) : MetaM Expr := do
    if valueIdx == values.size then
      return ← k ctorIndices vars
    let cases ← isos[valueIdx]!.constructors.mapIdxM fun ctorIdx ctor => do
      constructorTelescope (← inferType ctor) isos[valueIdx]!.t fun newVars => do
        mkLambdaFVars newVars (← loop (valueIdx + 1) (ctorIndices.push ctorIdx) (vars ++ newVars))
    let args := #[X] ++ cases ++ #[values[valueIdx]!]
    let result := Canonical.apply isos[valueIdx]!.recursor args.toList
    -- A recursive beta reduction is needed since we substitute lambdas into the
    -- recursors, and moreover, these lambdas may very well not be at the head
    -- of the expression.
    recursiveBetaReduce result
  loop 0 #[] #[]

/-
Example of above:
fun (X : Sort u)
    (f_0 : X)
    (f_1 : Nat -> X)
    (x : Option Nat) =>
      Option.rec Nat (fun (_ : Option.{0} Nat) => X)
      f_0
      (fun (val : Nat) => f_1 val)
      x
-/

def destructTrivial (t : Expr) : MetaM (Option Isomorphism) := do
  let ctor := Expr.lam `x t (Expr.bvar 0) .default
  let recursor ← mkRecursor t #[ctor] fun _ _ ctors input => do
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
  let recursor ← mkRecursor t constructors fun level X ctors input => do
    let builtinMotive := Expr.lam `_ t X .default
    let blockSizes := isoBlocks.map fun block => (block.map (·.constructors.size)).prod
    let ctorsBlocks := repackage ctors blockSizes
    let recBranches ← builtinCtors.mapIdxM fun caseIdx builtinCtor => do
      let choiceSizes := isoBlocks[caseIdx]!.map (·.constructors.size)
      constructorTelescope (← inferType builtinCtor) t fun values => do
        mkLambdaFVars values $ ← withRecurseOn X values isoBlocks[caseIdx]! fun indices vars => do
          let encodedIdx := encodeIndices choiceSizes indices
          return mkAppN ctorsBlocks[caseIdx]![encodedIdx]! vars
    return mkAppN (builtinRec level) (#[builtinMotive] ++ recBranches ++ #[input])
  return .some {
    t := t,
    constructors := constructors,
    recursor := recursor
  }

-- Will likely see some refactoring
-- Perhaps would be cool to move the input arguments to the end, but this is
-- also maybe counterintuitive
partial def destructPi (t : Expr) (inputType : Expr) (outputType : Expr) : MetaM (Option Isomorphism) := do
  let .some inputIso ← destruct inputType | return .none
  let .some outputIso ← destruct outputType | return .none
  let constituentTypes ← inputIso.constructors.mapM fun inputCtor => do
    constructorTelescope (← inferType inputCtor) inputType fun inputs => do
      withLocalDeclD `Y (Expr.sort (← mkFreshLevelMVar)) fun Y => do
        let recursified ← outputIso.constructors.mapM (recursify · Y outputType)
        withLocalDeclsDND' recursified fun outputs => do
          mkForallFVars (inputs ++ #[Y] ++ outputs) Y
  let constructor ← withLocalDeclsDND' constituentTypes fun constituents => do
    let resultLambda ← withLocalDeclD `x inputType fun input => do
      let caseArgs ← (inputIso.constructors.zip constituents).mapM fun (inputCtor, constituent) => do
        constructorTelescope (← inferType inputCtor) inputType fun inputs => do
          mkLambdaFVars inputs $ mkAppN constituent (inputs ++ #[outputType] ++ outputIso.constructors)
      -- See withRecurseOn for more on why we have to call recursiveBetaReduce
      let resultBody ← recursiveBetaReduce $ Canonical.apply inputIso.recursor (#[outputType] ++ caseArgs ++ #[input]).toList
      mkLambdaFVars #[input] resultBody
    mkLambdaFVars constituents resultLambda
  let recursor ← mkRecursor t #[constructor] fun _ X ctors input => do
    let ctor := ctors[0]!
    pure Inhabited.default
  return .some {
    t := t,
    constructors := #[constructor],
    recursor := recursor
  }

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
  let e := (Expr.lam `x (Expr.const `Bool []) (mkAppN (Expr.const `Option.some [0]) #[(Expr.const `Bool []), (Expr.bvar 0)]) .default)
  let t ← inferType e
  let iso := (← destruct t).get!
  IO.println $ ← ppExpr iso.constructors[0]!
  IO.println $ ← check iso.constructors[0]!
  )

#eval (do
  let e := toExpr ((.none, .none) : Option (Option Nat × Nat) × Option Nat)
  let t ← inferType e
  let iso := (← destruct t).get!
  IO.println $ ← iso.constructors.mapM ppExpr
  IO.println $ ← ppExpr iso.recursor
  IO.println $ ← check iso.recursor
  )

end
