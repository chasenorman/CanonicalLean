module

public import Lean
public import Canonical.Util
open Lean Core Meta

public section

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
  | .forallE _ inputType outputType _ =>
    return .some $ DestructInfo.pi inputType outputType
  | _ =>
    return .some DestructInfo.trivial

def constructorArity (ctor : Expr) (outputType : Expr) : MetaM Nat := do
  return (← inferType ctor).getForallArity - outputType.getForallArity

/-- Given `ctor` of the form `fun ..xs => body`, executes `k vs body`, where
    `vs` are free variables for `xs`. Similar to `lambdaTelescope`, except we
    account for the arity of `outputType`. -/
def constructorTelescope (ctor : Expr) (outputType : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let outputArity := outputType.getForallArity
  -- We use forallTelescope on the type here because `outputType` could be an
  -- arrow type, and moreover body could be either of the form `fun ys => A` or
  -- `f A`, so using lambdaTelescope isn't quite what we want.

  -- This is still a little bit ugly though; maybe we can use
  -- lambdaBoundedTelescope if we store the number of arguments in Isomorphism?
  forallTelescope (← inferType ctor) fun fvars _ => do
    let inputFVars := fvars.take (fvars.size - outputArity)
    let body := if ctor.isLambda then
      Canonical.apply ctor inputFVars.toList
    else
      mkAppN ctor inputFVars
    k inputFVars body

/-- Given an array `ctors` of constructors for `outputTypes`, the `i`th element
    of the form `fun ...xs[i], body[i]`, execute `k (vs[0] ++ ... ++ vs[n-1])
    #[body[0], ..., body[n-1]]`, where `vs[i]` are free variables for `xs[i]`. An
    iterated form of `constructorTelescope`. -/
def constructorTelescopeN (ctors : Array Expr) (outputTypes : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α :=
  ((ctors.zip outputTypes).foldl (fun k' (ctor, outputType) =>
    fun restVars bodies => constructorTelescope ctor outputType fun newVars body => k' (#[newVars] ++ restVars) (#[body] ++ bodies))
    k) #[] #[]

def constructorsTelescope (ctors : Array Expr) (outputType : Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α :=
  constructorTelescopeN ctors (ctors.map fun _ => outputType) k

/-- Takes a constructor `ctor` for `outputType` (i.e. a function with output type `outputType`)
    and a type `X` and returns the type of `ctor`, except the output type is
    replaced with `X`. This takes in the output type `outputType` to account for
    its arity.

    For example, if we recursify the constructor `id : (Nat -> Nat) -> (Nat ->
    Nat)` for `Nat -> Nat`, we obtain the type `(Nat -> Nat) -> X` -/
def simpleRecursify (ctor : Expr) (X : Expr) (outputType : Expr) : MetaM Expr := do
  constructorTelescope ctor outputType fun inputFVars _ => do
    mkForallFVars inputFVars X

def recursify (ctor : Expr) (motive : Expr) (outputType : Expr) : MetaM Expr := do
  constructorTelescope ctor outputType fun inputs packed => do
    mkForallFVars inputs (Expr.app motive packed)

/-- Given a type `t` and some constructors `ctors` for `t`, create free
    variables for a recursor type with level, constructors, and input, and then output a
    recursor of the correct type with body determined by executing `k` on these
    free variables. -/
def mkSimpleRecursor (t : Expr) (ctors : Array Expr) (k : Level → Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let level ← mkFreshLevelMVar
  withLocalDeclD `X (Expr.sort level) fun fvarX => do
    let ctorInfo ← ctors.mapIdxM fun i ctor => do
      pure (Name.mkSimple s!"f_{i}", fun _ => simpleRecursify ctor fvarX t)
    withLocalDeclsD ctorInfo fun fvarCtors => do
      withLocalDeclD `t t fun fvarInput => do
        mkLambdaFVars (#[fvarX] ++ fvarCtors ++ #[fvarInput]) (← k level fvarX fvarCtors fvarInput)

def mkRecursor (t : Expr) (ctors : Array Expr) (k : Level → Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let level ← mkFreshLevelMVar
  withLocalDeclD `motive (Expr.forallE `l t (Expr.sort level) .default) fun fvarMotive => do
    let ctorInfo ← ctors.mapIdxM fun i ctor => do
      pure (Name.mkSimple s!"f_{i}", fun _ => recursify ctor fvarMotive t)
    withLocalDeclsD ctorInfo fun fvarCtors => do
      withLocalDeclD `t t fun fvarInput => do
        mkLambdaFVars (#[fvarMotive] ++ fvarCtors ++ #[fvarInput]) (← k level fvarMotive fvarCtors fvarInput)

#eval show MetaM Unit from (do
  let ctor := (Expr.lam `f (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default) (Expr.bvar 0) .default)
  let t := (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default)
  let e ← mkRecursor t #[ctor] fun _ X ctors input => do
    return Expr.app ctors[0]! input
  IO.println $ ← ppExpr e
  )

/-- Returns a single index into an array of length `sizes.prod` based on
    `indices`, which effectively indexes into a Cartesian product. This function is
    the inverse of `decodeIndex`. -/
def encodeIndices (sizes : Array Nat) (indices : Array Nat) : Nat :=
  (sizes.zip indices).foldl (fun idx (size, i) => idx * size + i) 0

/-- Given an index into an array of length `sizes.prod`, returns an array of
    indices based on `i` that effectively index into a Cartesian product. This
    function is the inverse of `encodeIndices` -/
def decodeIndex (sizes : Array Nat) (i : Nat) : Array Nat :=
  (sizes.foldr (fun size (acc, idx) => (#[idx % size] ++ acc, idx / size)) (#[], i)).fst

/-- Executes `k` for each possible tuple of the form `(x_0, x_1, ..., x_n)`,
    where `x_i` is an element from `cases[i]!` -/
def withCartesianProductM [Inhabited α] [Monad n] (cases : Array (Array α)) (k : Array α → n β) : n (Array β) := do
  let sizes := cases.map (·.size)
  let totalSize := sizes.prod
  let mut result : Array β := Array.emptyWithCapacity totalSize
  for i in [:totalSize] do
    let indices := decodeIndex sizes i
    let values := cases.mapIdx fun i case => case[indices[i]!]!
    result := result.push (← k values)
  return result

/-- Takes an array `data` of total length equal to the sum of `sizes` and
    partitions it into blocks according to `sizes`. -/
def repackage (data : Array α) (sizes : Array Nat) : Array (Array α) :=
  (sizes.foldl (fun (packed, remaining) size =>
    (packed.push (remaining.take size), remaining.drop size))
    (#[], data)).fst

/-- Fully β-reduces subexpressions of `e`. -/
def recursiveBetaReduce (e : Expr) : MetaM Expr := do
  Meta.transform e (post := fun subexpr => do
    return TransformStep.done subexpr.headBeta
  )

def withLocalDeclsDND' [Inhabited α] (types : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
  withLocalDeclsDND (types.mapIdx fun i type => (Name.mkSimple s!"f_{i}", type)) k

end
