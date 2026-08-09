module

import Lean
public import Lean.Expr
public import Lean.Meta.Basic

open Lean Core Meta

namespace Destruct

public section

/-- A mapping between an expression `e` and its constituent expressions `e₁`,
    ..., `eₙ`.

    - The field `pack` is of the form `λ x₁ … xₙ ↦ ⟨…⟩`
    - The field `unpack` is of the form `#[λ x ↦ (…).1, …, λ x ↦ (…).n]`
-/
structure Bijection where
  pack : Expr
  unpack : Array Expr
  deriving Inhabited

def Bijection.pp (b : Bijection) : MetaM String := do
  let pack ← ppExpr b.pack
  let unpacked ← b.unpack.mapM fun e => do return " " ++ toString (← ppExpr e)
  let unpacked' := "\n".intercalate unpacked.toList
  return s!"\{\n pack := {pack},\n unpack := [\n  {unpacked'}\n ]\n}"

def apply (fn : Expr) (arg : Expr) : Expr :=
  match fn with
  | Expr.lam _ _ body _ => body.instantiate1 arg
  | _ => panic! s!"Destruct.apply expected a lambda, got {fn}"

def applyN (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (fun app arg => apply app arg) fn

mutual
def destructTrivial (t : Expr) (binderName : Name) : MetaM Bijection := do
  let id := Expr.lam binderName t (Expr.bvar 0) .default
  return ⟨id, #[id]⟩

def destructStruct (t : Expr) (binderName : Name)
  (fields : Nat) (builtinCtor : Expr) : MetaM Bijection := do
  return Inhabited.default

def destructPi (t : Expr) (binderName : Name)
  (inputName : Name) (inputType : Expr) (outputType : Expr) (inputInfo : BinderInfo) : MetaM Bijection := do
  return Inhabited.default

def destruct (t : Expr) (binderName : Name) : MetaM Bijection := do
  match t with
  | Expr.forallE inputName inputType outputType inputInfo =>
    destructPi t binderName inputName inputType outputType inputInfo
  | Expr.const _ _
  | Expr.app _ _ => do
    let headFn := t.getAppFn
    let headArgs := t.getAppArgs

    match headFn.constName? with
    | .none => destructTrivial t binderName
    | .some headName =>
      -- TODO: Destruct won't properly recognize single constructor inductives
      -- as structures if we do this. The code still currently checks this,
      -- however, because (unless I'm mistaken) Expr.proj, which is used in
      -- destructStruct, does not work for single constructor inductives.
      match getStructureInfo? (← getEnv) headName with
      | .none => destructTrivial t binderName
      | .some info =>
        let fields := info.fieldNames.size
        let headLevels := headFn.constLevels!
        let induct ← getConstInfoInduct headName
        let ctor := mkAppN (Expr.const induct.ctors[0]! headLevels) headArgs
        destructStruct t binderName fields (← etaExpand ctor)
  | _ => destructTrivial t binderName
end

#eval show MetaM Unit from (do
  let t := Expr.const `Nat []
  let b ← destruct t `e
  IO.println $ ← b.pp
)
