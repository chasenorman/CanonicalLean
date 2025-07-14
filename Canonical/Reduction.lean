import Canonical.Basic
import Canonical.Util
import Canonical.Monomorphize

open Lean hiding Term
open Meta Std

namespace Canonical

def wildcard : Term := { spine := { head := "*" } }

def varToTerm (v : Var) : Term := { spine := { head := v.name } }

partial def containsLambda (t : Term) : Bool :=
  !t.params.isEmpty || t.spine.args.any containsLambda

partial def count (t : Spine) (v : String) : Nat :=
  t.args.foldl (init := if t.head == v then 1 else 0) (· + count ·.spine v)

def validSimpLemma (xs : Array Expr) (rule : Rule) : MetaM Bool := do
  if ← xs.anyM (fun x => do pure ((← typeArity1 (← x.fvarId!.getType)) != 0)) then
    pure false -- higher order
  else if ← xs.anyM (fun x => do pure (count rule.lhs (← toNameString x) != 1)) then
    pure false -- unbound or overused variable
  else if rule.lhs.args.any containsLambda then
    pure false -- potentially requires that the lambda does not use the fvars
  else pure true

/-- Rule corresponding to reduction of projections. -/
def projRule (projection : String) (projInfo : ProjectionFunctionInfo) (constructor : String) (constructorVal : ConstructorVal) (arity : Nat) : Rule :=
  let ctorArgs : Array Term := (Array.replicate (constructorVal.numParams + constructorVal.numFields) wildcard).set! (constructorVal.numParams + projInfo.i) { spine := { head := "field" } }
  let fieldArgs : Array Term := Array.ofFn (fun (i : Fin (arity - projInfo.numParams - 1)) => { spine := { head := "arg" ++ toString i.val } })
  let args : Array Term := ((Array.replicate projInfo.numParams wildcard).push { spine := { head := constructor, args := ctorArgs } }) ++ fieldArgs
  ⟨{ head := projection, args := args }, { head := "field", args := fieldArgs }, #[], true⟩


/-- Rule corresponding to ι-reduction -/
def recRule (recursor : Name) (recVal : RecursorVal) (constructor : Name) (constructorVal : ConstructorVal) (rhs : Term) : Rule :=
  let ctorStart := (recVal.numParams+recVal.numMotives+recVal.numMinors);
  let args : Array Term := (rhs.params.shrink ctorStart).map varToTerm
  let ctorArgs : Array Term := (rhs.params.toSubarray ctorStart (ctorStart + constructorVal.numFields)).toArray.map varToTerm
  let major : Spine := { head := constructor.toString, args := Array.replicate constructorVal.numParams wildcard ++ ctorArgs}
  let args : Array Term := (args ++ Array.replicate recVal.numIndices wildcard).push { spine := major}
  let args := args ++ (rhs.params.toSubarray (ctorStart + constructorVal.numFields)).toArray.map varToTerm
  ⟨{head := recursor.toString, args := args }, rhs.spine, #[], true⟩

/-- Rule corresponding to δ-reduction. -/
def defRule (name : String) (defn : Term) : Rule :=
  ⟨{ head := name, args := defn.params.map varToTerm }, defn.spine, #[], false⟩

/-- Rules for the equality of distinct constructors to reduce to `False`. -/
def reduceCtorEqRules (ind : Name) (info : InductiveVal) : MetaM (Array Rule) := do
  let mut rules := #[]
  for ctor1 in info.ctors do
    for ctor2 in info.ctors do
      if ctor1 != ctor2 then
        let info1 ← getConstInfoCtor ctor1
        let info2 ← getConstInfoCtor ctor2
        let args1 := Array.replicate (info1.numFields + info.numParams + info.numIndices) wildcard
        let args2 := Array.replicate (info2.numFields + info.numParams + info.numIndices) wildcard
        rules := rules.push ⟨{ head := "Eq", args := #[
          { spine := { head := ind.toString } },
          { spine := { head := ctor1.toString, args := args1 } },
          { spine := { head := ctor2.toString, args := args2 } }
        ] }, { head := "False" }, #["reduceCtorEq"], true⟩
  pure rules
