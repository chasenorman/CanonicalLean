module

public import Canonical.Basic
public import Lean.Meta.Basic
public import Lean.ProjFns
import Canonical.Util

open Lean
open Meta Std

namespace Canonical

public section

/-- Placeholder for a term, not a reserved symbol. -/
def wildcard : Canonical.Expr := { spine := { head := "*" } }

/-- Creates an η-**short** `Expr` applying `d` at the head. -/
def Decl.toExpr (d : Decl) : Canonical.Expr := { spine := { head := d.name } }

partial def containsLambda (t : Canonical.Expr) : Bool :=
  !t.params.isEmpty || t.spine.args.any containsLambda

/-- Counts the occurrences of `v` as a head symbol in `t`. -/
partial def count (t : Spine) (v : String) : Nat :=
  t.args.foldl (init := if t.head == v then 1 else 0) (· + count ·.spine v)

/-- Filtering for candidate simp lemmas based on the `lhs`. -/
def validSimpLemma (xs : Array Lean.Expr) (lhs : Spine) : MetaM Bool := do
  if ← xs.anyM (fun x => do pure ((← typeArity1 (← x.fvarId!.getType)) != 0)) then
    pure false -- higher order
  else if ← xs.anyM (fun x => do pure (count lhs (← toNameString x) != 1)) then
    pure false -- unbound or overused variable
  else if lhs.args.any containsLambda then
    pure false -- potentially requires that the lambda does not use the fvars
  else pure true

/-- Rule corresponding to reduction of projections. -/
def projRule (projection : String) (projInfo : ProjectionFunctionInfo) (constructor : String) (constructorVal : ConstructorVal) (arity : Nat) : Rule :=
  let ctorArgs : Array Canonical.Expr := (Array.replicate (constructorVal.numParams + constructorVal.numFields) wildcard).set! (constructorVal.numParams + projInfo.i) { spine := { head := "field" } }
  let fieldArgs : Array Canonical.Expr := Array.ofFn (fun (i : Fin (arity - projInfo.numParams - 1)) => { spine := { head := "arg" ++ toString i.val } })
  let args : Array Canonical.Expr := ((Array.replicate projInfo.numParams wildcard).push { spine := { head := constructor, args := ctorArgs } }) ++ fieldArgs
  ⟨{ head := projection, args := args }, { head := "field", args := fieldArgs }, #[], true⟩

/-- Rule corresponding to ι-reduction -/
def recRule (recursor : Name) (recVal : RecursorVal) (constructor : Name) (constructorVal : ConstructorVal) (rhs : Canonical.Expr) : Rule :=
  let ctorStart := (recVal.numParams+recVal.numMotives+recVal.numMinors);
  let args : Array Canonical.Expr := (rhs.params.shrink ctorStart).map Decl.toExpr
  let ctorArgs : Array Canonical.Expr := (rhs.params.toSubarray ctorStart (ctorStart + constructorVal.numFields)).toArray.map Decl.toExpr
  let major : Spine := { head := constructor.toString, args := Array.replicate constructorVal.numParams wildcard ++ ctorArgs}
  let args : Array Canonical.Expr := (args ++ Array.replicate recVal.numIndices wildcard).push { spine := major }
  let args := args ++ (rhs.params.toSubarray (ctorStart + constructorVal.numFields)).toArray.map Decl.toExpr
  ⟨{head := recursor.toString, args := args }, rhs.spine, #[], true⟩

/-- Rule corresponding to δ-reduction. -/
def defRule (name : String) (defn : Canonical.Expr) : Rule :=
  ⟨{ head := name, args := defn.params.map Decl.toExpr }, defn.spine, #[], false⟩

/-- Rules for the equality of distinct constructors to reduce to `False`. -/
def reduceCtorEqRules (ind : Name) (info : InductiveVal) : MetaM (Array Rule) := do
  let mut rules := #[]
  for ctor1 in info.ctors do
    for ctor2 in info.ctors do
      if ctor1 != ctor2 then
        let info1 ← getConstInfoCtor ctor1
        let info2 ← getConstInfoCtor ctor2
        let args1 := Array.replicate (info1.numFields + info1.numParams) wildcard
        let args2 := Array.replicate (info2.numFields + info2.numParams) wildcard
        rules := rules.push ⟨{ head := "Eq", args := #[
          { spine := { head := ind.toString } },
          { spine := { head := ctor1.toString, args := args1 } },
          { spine := { head := ctor2.toString, args := args2 } }
        ] }, { head := "False" }, #["reduceCtorEq"], true⟩
  pure rules
