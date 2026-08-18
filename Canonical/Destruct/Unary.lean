module

import Lean
public import Lean.Expr
public import Lean.Meta.Basic

open Lean Core Meta

namespace Destruct

public section

abbrev DestructM := ReaderT NameSet MetaM

/-- A mapping between an expression `e` and its constituent expressions `e₁`,
    ..., `eₙ`.

    - The field `pack` is of the form `λ x₁ … xₙ ↦ ⟨…⟩`
    - The field `unpack` is of the form `#[λ x ↦ (…).1, …, λ x ↦ (…).n]`
-/
structure Bijection where
  pack : Expr
  unpack : Array Expr
  deriving Inhabited

-- Printing
def Bijection.p (b : Bijection) : String :=
  let pack := b.pack
  let unpack := b.unpack.map fun e => s!"{e}"
  let unpack' := "\n  ".intercalate unpack.toList
  s!"\{\n pack := {pack},\n unpack := [\n  {unpack'}\n ]\n}"

def Bijection.pp (b : Bijection) : MetaM String := do
  let pack ← ppExpr b.pack
  let unpack ← b.unpack.mapM fun e => do return toString (← ppExpr e)
  let unpack' := "\n  ".intercalate unpack.toList
  return s!"\{\n pack := {pack},\n unpack := [\n  {unpack'}\n ]\n}"

-- Utils
def apply (fn : Expr) (arg : Expr) : Expr :=
  match fn with
  | Expr.lam _ _ body _ => body.instantiate1 arg
  | _ => panic! s!"Destruct.apply expected a lambda, got {fn}"

def applyN (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (fun app arg => apply app arg) fn

def lambdaBinders (lam : Expr) (n : Nat) : List (Name × Expr) :=
  if n == 0 then [] else
  match lam with
  | Expr.lam name type body _ => (name, type)::lambdaBinders body (n-1)
  | _ => panic! s!"Destruct.lambdaBinders expected a lambda, got {lam}"

partial def packTelescope (bijs : Array Bijection) (fvars : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α := do
  let rec recurse (i : Nat) (varBlocks : Array (Array Expr)) (packedBlocks : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α := do
    if i == bijs.size then return ← k varBlocks packedBlocks
    let b := bijs[i]!
    let pack := b.pack.replaceFVars (fvars.take i) packedBlocks
    lambdaBoundedTelescope pack b.unpack.size fun vars packed => do
      recurse (i + 1) (varBlocks.push vars) (packedBlocks.push packed) k
  recurse 0 #[] #[] k

def destructTrivial (t : Expr) (binderName : Name) : DestructM Bijection := do
  let id := Expr.lam binderName t (Expr.bvar 0) .default
  return ⟨id, #[id]⟩

def destructAdhoc (t : Expr) (binderName : Name) (headName : Name) : DestructM Bijection := do
  let fn := t.getAppFn
  let _args := t.getAppArgs

  if headName == ``True then
    return ⟨Expr.const ``True.intro [], #[]⟩
  else if headName == ``Unit then
    return ⟨Expr.const ``Unit.unit [], #[]⟩
  else if headName == ``PUnit then
    return ⟨Expr.const ``PUnit.unit fn.constLevels!, #[]⟩
  -- TODO: Handle single constructor inductives like Exists correctly

  destructTrivial t binderName

mutual
partial def destructStruct (t : Expr) (binderName : Name)
  (structName : Name) (numFields : Nat) (builtinCtor : Expr) : DestructM Bijection := do
  lambdaBoundedTelescope builtinCtor numFields fun fvars packed => do
    let lctx ← getLCtx
    let fvarInfo := fvars.map fun fvar => lctx.get! fvar.fvarId!
    let types := fvarInfo.map (·.type)
    let names := fvarInfo.map (·.userName)
    let bijs ← (types.zip names).mapM fun (type, name) => destruct type name

    let pack ← packTelescope bijs fvars fun varBlocks packedBlocks => do
      mkLambdaFVars varBlocks.flatten (packed.replaceFVars fvars packedBlocks)

    let unpack ← withLocalDecl binderName .default t fun fvar => do
      let projs := (Array.range numFields).map (Expr.proj structName · fvar)
      let unpacks ← (bijs.zip projs).mapM fun (b, proj) => do
        b.unpack.mapM fun lam => do
          -- TODO: is this line actually needed? Is there a situation in which
          -- the body of an unpack can contain free variables from `fvars`?
          let lam' := lam.replaceFVars fvars projs
          mkLambdaFVars #[fvar] (apply lam' proj)
      return unpacks.flatten

    return ⟨pack, unpack⟩

partial def destructPi (t : Expr) (binderName : Name)
  (inputName : Name) (inputType : Expr) (outputType : Expr) (inputInfo : BinderInfo) : DestructM Bijection := do
  let input ← destruct inputType inputName
  lambdaBoundedTelescope input.pack input.unpack.size fun vars packed => do
    -- TODO: Is binderName the correct thing to put here? (I think not)
    let output ← destruct (outputType.instantiate1 packed) binderName

    let unpack ← withLocalDecl binderName .default t fun f => do
      output.unpack.mapM fun field => mkLambdaFVars (#[f] ++ vars) (apply field (f.app packed))

    let types := (lambdaBinders output.pack output.unpack.size).toArray.map fun (name, type) =>
      (name, .default, fun fs => do mkForallFVars vars (type.instantiate (fs.map fun f => mkAppN f vars)))

    withLocalDecls types fun fs => do
      let body := applyN output.pack (fs.map (mkAppN · vars))
      withLocalDecl inputName inputInfo inputType fun var => do
        let replaced := body.replaceFVars vars (input.unpack.map (apply · var))
        let pack ← mkLambdaFVars (fs.push var) replaced
        return ⟨pack, unpack⟩

partial def destructApp (t : Expr) (binderName : Name) (headFn : Expr) (headArgs : Array Expr) : DestructM Bijection := do
  if headFn.constName?.isNone then return ← destructTrivial t binderName
  let headName := headFn.constName!

  if (← read).contains headName then
    let info := getStructureInfo (← getEnv) headName
    let fields := info.fieldNames.size
    let headLevels := headFn.constLevels!
    let induct ← getConstInfoInduct headName
    let ctor ← etaExpand (Expr.const induct.ctors[0]! headLevels)
    return ← destructStruct t binderName headName fields (applyN ctor headArgs)

  destructAdhoc t binderName headName

partial def destruct (t : Expr) (binderName : Name) : DestructM Bijection := do
  if t.isForall then
    destructPi t binderName t.bindingName! t.bindingDomain! t.bindingBody! t.bindingInfo!
  else if t.isConst || t.isApp then
    destructApp t binderName t.getAppFn t.getAppArgs
  else
    destructTrivial t binderName
end

/--
TODO:
-> What exactly is going on with destructTactic (why is output List (⋯ × MVarId)?)
-> Obtain fun examples for paper?
-/

structure Bundle (X : Type) (p : X → Prop) where
  value : X
  proof : p value

theorem example_theorem : ∀ (n : Nat), n * n = 1 ↔ n = 1 := by sorry

#eval show MetaM Unit from ReaderT.run (do
  -- Unit -> Nat -> Nat
  -- let t := Expr.forallE `n (Expr.const `Unit []) (Expr.forallE `m (Expr.const `Nat []) (Expr.const `Nat []) .default) .default

  -- let t := Expr.forallE `n (Expr.const `Nat []) (Expr.const `Nat []) .default

  -- let t := Expr.forallE `p p (mkAppN (Expr.const `Exists [1]) #[Expr.const `Nat [], Expr.bvar 0]) .default

  -- (X : Type) → Bundle X (fun (x : X) → x = x)
  -- let t := Expr.forallE `X (Expr.sort 1) (mkAppN (Expr.const ``Bundle []) #[Expr.bvar 0, Expr.lam `x (Expr.bvar 0) (mkAppN (Expr.const `Eq [1]) #[Expr.bvar 1, Expr.bvar 0, Expr.bvar 0]) .default]) .default

  -- ∀ n : Nat, n * n = 1 ↔ n = 1
  let t ← inferType (Expr.const ``example_theorem [])
  let b ← destruct t `x
  IO.println $ ← b.pp
  IO.println $ ← check b.pack
  IO.println $ ← b.unpack.mapM (fun e => do check e)
) (NameSet.ofArray #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array])
