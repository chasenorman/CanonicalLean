module

public import Lean
open Lean Core Meta

public section

inductive DestructInfo where
  | trivial
  | induct (builtinCtors : Array Expr) (builtinRec : Level → Expr)
  | pi (inputTypes : Array Expr) (outputType : Expr)
  deriving Inhabited

def extractInfo (t : Expr) : MetaM (Option DestructInfo) := do
  if !(← inferType t).isSort then return .none
  let t' ← whnf t
  match t' with
  | .const _ _
  | .app _ _ => do
    -- In the case that there is a dependent type, the head will be a free
    -- variable, not a constant, so we will return the trivial constructor
    let .some headName := t'.getAppFn.constName? | return .some .trivial
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

def constructorArity (type : Expr) (outputType : Expr) : Nat :=
  type.getForallArity - outputType.getForallArity

/-- Given `type` of the form `forall xs, outputType`, executes `k vs`, where
    `vs` are free variables for `xs`. Similar to `forallTelescope`, except we
    account for the arity of `outputType`. -/
def constructorTelescope (type : Expr) (outputType : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let outputArity := outputType.getForallArity
  forallTelescope type fun fvars _ => do
    let inputFVars := fvars.take (fvars.size - outputArity)
    k inputFVars

/-- Given an array `types`, the `i`th element of the form `forall xs[i],
    outputType`, execute `k (vs[0] ++ ... ++ vs[n-1])`, where `vs[i]` are free
    variables for `xs[i]`. An iterated form of `constructorTelescope`. -/
def constructorTelescopeN (types : Array Expr) (outputTypes : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  ((types.zip outputTypes).foldl (fun k' (type, outputType) =>
    fun restVars => constructorTelescope type outputType fun newVars => k' (restVars ++ newVars))
    k) #[]
  -- (types.foldr (fun type k' =>
  --   fun restVars => constructorTelescope type outputType fun newVars => k' (newVars ++ restVars))
  --   k) #[]

/-- Takes a constructor `ctor` for `outputType` (i.e. a function with output type `outputType`)
    and a type `X` and returns the type of `ctor`, except the output type is
    replaced with `X`. This takes in the output type `outputType` to account for
    its arity.

    For example, if we recursify the constructor `id : (Nat -> Nat) -> (Nat ->
    Nat)` for `Nat -> Nat`, we obtain the type `(Nat -> Nat) -> X` -/
def recursify (ctor : Expr) (X : Expr) (outputType : Expr) : MetaM Expr := do
  constructorTelescope (← inferType ctor) outputType fun inputFVars => do
    mkForallFVars inputFVars X

#eval show MetaM Unit from (do
  IO.println $ ← recursify (Expr.lam `f (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default) (Expr.bvar 0) .default) (Expr.const `X []) (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default)
)

/-- Given a type `t` and some constructors `ctors` for `t`, create free
    variables for a recursor type with level, constructors, and input, and then output a
    recursor of the correct type with body determined by executing `k` on these
    free variables. -/
def withRecursor (t : Expr) (ctors : Array Expr) (k : Level → Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let level ← mkFreshLevelMVar
  withLocalDeclD `X (Expr.sort level) fun fvarX => do
    let ctorInfo ← ctors.mapIdxM fun i ctor => do
      pure (Name.mkSimple s!"f_{i}", fun _ => recursify ctor fvarX t)
    withLocalDeclsD ctorInfo fun fvarCtors => do
      withLocalDeclD `x t fun fvarInput => do
        mkLambdaFVars (#[fvarX] ++ fvarCtors ++ #[fvarInput]) (← k level fvarX fvarCtors fvarInput)

#eval show MetaM Unit from (do
  let ctor := (Expr.lam `f (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default) (Expr.bvar 0) .default)
  let t := (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default)
  let e ← withRecursor t #[ctor] fun _ X ctors input => do
    return Expr.app ctors[0]! input
  IO.println $ ← ppExpr e
  )

def encodeIndices (sizes : Array Nat) (indices : Array Nat) : Nat :=
  (sizes.zip indices).foldl (fun idx (size, i) => idx * size + i) 0

def decodeIndex (sizes : Array Nat) (i : Nat) : Array Nat :=
  (sizes.foldr (fun size (acc, idx) => (#[idx % size] ++ acc, idx / size)) (#[], i)).fst

def withCartesianProductM [Inhabited α] [Monad n] (cases : Array (Array α)) (k : Array α → n β) : n (Array β) := do
  let sizes := cases.map (·.size)
  let totalSize := sizes.prod
  let mut result : Array β := Array.emptyWithCapacity totalSize
  for i in [:totalSize] do
    let indices := decodeIndex sizes i
    let values := cases.mapIdx fun i case => case[indices[i]!]!
    result := result.push (← k values)
  return result

def repackage (data : Array α) (sizes : Array Nat) : Array (Array α) :=
  (sizes.foldl (fun (packed, remaining) size =>
    (packed.push (remaining.take size), remaining.drop size))
    (#[], data)).fst
end
