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

/-- Counts the occurrences of `v` as a head symbol in `t`. -/
partial def count (t : Spine) (v : String) : Nat :=
  t.args.foldl (init := if t.head == v then 1 else 0) (· + count ·.spine v)

/-- Whether `t` is the η-expansion of the variable `v`. -/
partial def isEta (v : String) (t : Canonical.Expr) : Bool :=
  t.spine.head == v && t.params.size == t.spine.args.size &&
    (t.params.zip t.spine.args).all fun (p, a) => isEta p.name a

/-- Whether the argument `t` can be matched, binding the variables `vars`:
    it is a variable, or a λ-free application of a symbol to such arguments. -/
partial def patternArg (vars : Array String) (t : Canonical.Expr) : Bool :=
  vars.any (isEta · t) || (t.params.isEmpty && !vars.contains t.spine.head && t.spine.args.all (patternArg vars))

/-- Filtering for candidate simp lemmas based on the `lhs`. -/
def validSimpLemma (xs : Array Lean.Expr) (lhs : Spine) : MetaM Bool := do
  let vars ← xs.mapM toNameString
  pure (vars.all (count lhs · == 1) && lhs.args.all (patternArg vars))

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
          { spine := { head := ind.toString, args := Array.replicate (info.numParams + info.numIndices) wildcard } },
          { spine := { head := ctor1.toString, args := args1 } },
          { spine := { head := ctor2.toString, args := args2 } }
        ] }, { head := "False" }, #["reduceCtorEq"], true⟩
  pure rules
