module


public import Lean
open Lean Core Meta

public section

/-- Given `type` of the form `forall xs, outputType`, executes `k vs`, where
    `vs` are free variables for `xs`. Similar to `forallTelescope`, except we
    account for the arity of `outputType`. -/
def constructorTelescope (type : Expr) (outputType : Expr) (k : Array Expr → MetaM α) : MetaM α := do
  let outputArity := outputType.getForallArity
  forallTelescope type fun fvars _ => do
    let inputFVars := fvars.take (fvars.size - outputArity)
    k inputFVars

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
    variables for a recursor type, constructors, and input, and then output a
    recursor of the correct type with body determined by executing `k` on these
    free variables. -/
def withRecursor (t : Expr) (ctors : Array Expr) (k : Expr → Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let level ← mkFreshLevelMVar
  withLocalDeclD `X (Expr.sort level) fun fvarX => do
    let ctorInfo ← ctors.mapIdxM fun i ctor => do
      pure (Name.mkSimple s!"f_{i}", fun _ => recursify ctor fvarX t)
    withLocalDeclsD ctorInfo fun fvarCtors => do
      withLocalDeclD `x t fun fvarInput => do
        mkLambdaFVars (#[fvarX] ++ fvarCtors ++ #[fvarInput]) (← k fvarX fvarCtors fvarInput)

#eval show MetaM Unit from (do
  let ctor := (Expr.lam `f (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default) (Expr.bvar 0) .default)
  let t := (Expr.forallE `_ (Expr.const `Nat []) (Expr.const `Nat []) .default)
  let e ← withRecursor t #[ctor] fun X ctors input => do
    return Expr.app ctors[0]! input
  IO.println $ ← ppExpr e
  )
end
