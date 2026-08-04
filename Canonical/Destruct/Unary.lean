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
  -- `true` if the recursor takes in an unparameterized motive and `false`
  -- otherwise
  hasSimpleRecursor : Bool
  deriving Inhabited

/-- Returns an expression of nested recursor calls that recurse on `values` in
    sequence, executing `k` on all possible branching cases. -/
-- partial def withRecurseOn (X : Expr) (values : Array Expr) (isos : Array Isomorphism) (k : Array Nat → Array Expr → MetaM Expr) : MetaM Expr := do
--   let rec loop (valueIdx : Nat) (ctorIndices : Array Nat) (vars : Array Expr) : MetaM Expr := do
--     if valueIdx == values.size then
--       return ← k ctorIndices vars
--     let cases ← isos[valueIdx]!.constructors.mapIdxM fun ctorIdx ctor => do
--       constructorTelescope ctor isos[valueIdx]!.t fun newVars _ => do
--         mkLambdaFVars newVars (← loop (valueIdx + 1) (ctorIndices.push ctorIdx) (vars ++ newVars))
--     let args := #[X] ++ cases ++ #[values[valueIdx]!]
--     let result := Canonical.apply isos[valueIdx]!.recursor args.toList
--     -- A recursive beta reduction is needed since we substitute lambdas into the
--     -- recursors, and moreover, these lambdas may very well not be at the head
--     -- of the expression. A potential idea to fix this might be to have some of
--     -- the recursor arguments eta-reduced
--     recursiveBetaReduce result
--   loop 0 #[] #[]


def destructTrivial (t : Expr) : MetaM Isomorphism := do
  let constructor := Expr.lam `x t (Expr.bvar 0) .default
  let recursor ← mkRecursor t #[constructor] fun _ _ ctors input => do
    return Expr.app ctors[0]! input
  return {
    t := t,
    constructors := #[constructor],
    recursor := recursor,
    hasSimpleRecursor := false
  }

mutual
-- partial def destructCtor (t : Expr) (ctor : Expr) : MetaM (Option (Array Isomorphism)) := do
--   let optIsos ← constructorTelescope ctor t fun fvars _ => do
--     fvars.mapM fun input => do destruct (← inferType input)
--   return optIsos.mapM id

partial def destructInduct (t : Expr) (builtinCtors : Array Expr) (builtinRec : Level → Expr) : MetaM Isomorphism := do
  destructTrivial t

partial def destructPi (t : Expr) (inputType : Expr) (outputType : Expr) : MetaM Isomorphism := do
  let inputIso ← destruct inputType
  let (constructor, recursor) ← (constructorsTelescope inputIso.constructors inputType fun inputCases packedCases => do
    let outputTypes := packedCases.map fun packed => outputType.instantiate1 packed
    let outputIsos ← outputTypes.mapM destruct

    let constituentTypes ← (inputCases.zip outputIsos).mapM fun (inputCase, outputIso) => do
      withLocalDeclD `Y (Expr.sort (← mkFreshLevelMVar)) fun Y => do
        -- The different branches of an inductive explicitly do not dependent on
        -- each other
        let recursified ← outputIso.constructors.mapM (simpleRecursify · Y outputIso.t)
        withLocalDeclsDND' recursified fun ctors => do
          mkForallFVars (inputCase ++ #[Y] ++ ctors) Y

    -- The constituent types do not depend on each other
    let constructor ← withLocalDeclsDND' constituentTypes fun constituents => do
      withLocalDeclD `y inputType fun input => do
        let cases ← inputCases.mapIdxM fun i inputVars => do
          let specificType := outputTypes[i]!
          let specificIso := outputIsos[i]!
          let branchBody := mkAppN constituents[i]! (inputVars ++ #[specificType] ++ specificIso.constructors)
          mkLambdaFVars inputVars branchBody
        let motive := if inputIso.hasSimpleRecursor then
          outputType.instantiate1 input
        else
          Expr.lam `a inputType outputType .default
        let body := Canonical.apply inputIso.recursor (#[motive] ++ cases ++ #[input]).toList
        mkLambdaFVars (constituents.push input) body

    -- This should definitely be refactored
    let recursor ← mkSimpleRecursor t #[constructor] fun _ _ ctors f => do
      let ctor := ctors[0]!
      let projs ← constituentTypes.mapIdxM fun i constituentType => do
        let specificIso := outputIsos[i]!
        forallTelescope constituentType fun constituentInputs _ => do
          let numInputs ← constructorArity inputIso.constructors[i]! inputType
          let (unpacked, Y, recursified) := (
            constituentInputs.take numInputs,
            constituentInputs[numInputs]!,
            constituentInputs.drop (numInputs + 1)
          )
          let specificType := specificIso.t.replaceFVars inputCases[i]! unpacked
          let specificRecursor := specificIso.recursor.replaceFVars inputCases[i]! unpacked
          let motive := if specificIso.hasSimpleRecursor then Y
            else Expr.lam `_ specificType Y .default
          let app := Expr.app f $ Canonical.apply inputIso.constructors[i]! unpacked.toList
          let body := Canonical.apply specificRecursor (#[motive] ++ recursified ++ #[app]).toList
          mkLambdaFVars constituentInputs body
      return mkAppN ctor projs

    return (constructor, recursor)
  )
  return {
    t,
    constructors := #[constructor],
    recursor,
    hasSimpleRecursor := true
  }

partial def destruct (t : Expr) : MetaM Isomorphism := do
  if !(← inferType t).isSort then panic! s!"Tried to call destruct on non-sort expression {t}"
  let t ← whnf t
  let optInfo ← extractInfo t
  if optInfo.isNone then return ← destructTrivial t

  match optInfo.get! with
  | .trivial => do
    destructTrivial t
  | .induct builtinCtors builtinRec => do
    destructInduct t builtinCtors builtinRec
  | .pi inputType outputType => destructPi t inputType outputType
end

#eval (do
  let on := Expr.app (Expr.const `Option [0]) (Expr.const `Nat [])
  let pon := mkAppN (Expr.const `Prod [0, 0]) #[on, (Expr.const `Unit [])]
  let t := (Expr.forallE `v pon (Expr.const ``Nat []) .default)
  let iso ← destruct t
  IO.println $ ← ppExpr (← recursiveBetaReduce iso.constructors[0]!)
  IO.println $ ← ppExpr (← recursiveBetaReduce iso.recursor)
  IO.println ""

  let t := (Expr.forallE `A (Expr.sort 0) (mkAppN (Expr.const `Not []) #[Expr.bvar 0]) .default)
  let iso ← destruct t
  IO.println $ (← recursiveBetaReduce iso.constructors[0]!)
  IO.println ""
  IO.println $ (← recursiveBetaReduce iso.recursor)
  )

-- Examples.
-- def constructor1 : Nat → Option Nat × Nat := fun m => (.none, m)
-- def constructor2 : Nat → Nat → Option Nat × Nat := fun n m => (.some n, m)
--
-- noncomputable def recursor.{u}
--   (motive : Option Nat × Nat → Sort u)
--   (f1 : (m : Nat) → motive (constructor1 m))
--   (f2 : (n : Nat) → (m : Nat) → motive (constructor2 n m)) :
--   (x : Option Nat × Nat) → motive x :=
--     Prod.rec (motive := motive) fun (l : Option Nat) (m : Nat) =>
--       Option.rec (motive := fun l' => motive (l', m))
--       (f1 m)
--       (fun n => f2 n m)
--       l
--
-- def T (x : Option Nat × Nat) : Type :=
--   if x.1.isSome then Nat else Unit
--
-- -- Type is (x : Option Nat × Nat) → T x
-- noncomputable def constructorForPiType :
--   ((m : Nat) → T (constructor1 m)) → ((n : Nat) → (m : Nat) → T (constructor2 n m)) → (x : Option Nat × Nat) → T x :=
--   fun f1 f2 x => recursor (motive := T) f1 f2 x
--
-- noncomputable def recursorForPiType.{u}
--   (X : Sort u)
--   (c : ((m : Nat) → T (constructor1 m)) → ((n : Nat) → (m : Nat) → T (constructor2 n m)) → X)
--   (f : (x : Option Nat × Nat) → T x) : X :=
--     c (fun (m : Nat) => f (constructor1 m)) (fun (n : Nat) (m : Nat) => f (constructor2 n m))
