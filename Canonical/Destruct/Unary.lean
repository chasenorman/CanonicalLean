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

def Bijection.p (b : Bijection) : String :=
  let pack := b.pack
  let unpack := b.unpack.map fun e => s!"{e}"
  let unpack' := "\n".intercalate unpack.toList
  s!"\{\n pack := {pack},\n unpack := [\n  {unpack'}\n ]\n}"

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
partial def destructTrivial (t : Expr) (binderName : Name) : MetaM Bijection := do
  let id := Expr.lam binderName t (Expr.bvar 0) .default
  return ⟨id, #[id]⟩

partial def destructStruct (t : Expr) (binderName : Name)
  (fields : Nat) (builtinCtor : Expr) : MetaM Bijection := do
  destructTrivial t binderName

partial def destructPi (t : Expr) (binderName : Name)
  (inputName : Name) (inputType : Expr) (outputType : Expr) (inputInfo : BinderInfo) : MetaM Bijection := do
  let input ← destruct inputType inputName
  lambdaBoundedTelescope input.pack input.unpack.size fun vars packed => do
    -- TODO: Is binderName the correct thing to put here? (I think not)
    let output ← destruct (outputType.instantiate1 packed) binderName

    let unpack ← withLocalDecl binderName .default t fun f => do
      output.unpack.mapM fun field => mkLambdaFVars (#[f] ++ vars) (apply field (f.app packed))

    -- TODO: Chase's implementation maps over output.unpack and gives the
    -- type for `field` as `field.bindingDomain!.abstract vars`. This cannot be
    -- correct since if `t` is something like `Nat → Nat`, `types` would
    -- look like `#[Nat]` instead of `#[Nat → Nat]`, causing `pack` (via `fs`
    -- below) to look like `fun (x : Nat) (n : Nat) => x n` (definitely wrong).
    -- Perhaps I could be misinterpreting why `.abstract` was originally used
    -- above instead of `mkLambdaFVars`?
    --
    -- This implementation maps over `unpack` and then takes the output type of
    -- each projection, which I believe is technically correct but also looks
    -- very suspicious. Ideally we should be able to do away with `inferType`.
    let types := unpack.map fun field =>
      (field.bindingName!, .default, fun _ => do pure (← inferType field).bindingBody!)

    withLocalDecls types fun fs => do
      let body := applyN output.pack (fs.map (mkAppN · vars))
      withLocalDecl inputName inputInfo inputType fun var => do
        let replaced := body.replaceFVars vars (input.unpack.map (apply · var))
        let pack ← mkLambdaFVars (fs.push var) replaced
        return ⟨pack, unpack⟩

partial def destruct (t : Expr) (binderName : Name) : MetaM Bijection := do
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

structure Bundle (p : Nat → Prop) where
  value : Nat
  proof : p value

#eval show MetaM Unit from (do
  let p := Expr.forallE `n (Expr.const `Nat []) (Expr.sort 0) .default
  let t := Expr.forallE `p p (mkAppN (Expr.const ``Bundle []) #[Expr.bvar 0]) .default
  IO.println t
  IO.println $ ← check t
  -- let t := Expr.forallE `n (Expr.const `Nat []) (Expr.forallE `m (Expr.const `Nat []) (Expr.const `Nat []) .default) .default
  -- let t := Expr.forallE `n (Expr.const `Nat []) (Expr.const `Nat []) .default
  let b ← destruct t `x
  IO.println b.p
)
