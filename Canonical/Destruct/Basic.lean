module

import Lean
import Canonical.Util
import Canonical.Symbols
public import Lean.Meta.Basic
public meta import Canonical.Destruct.Util
public import Canonical.Destruct.Translation

open Lean Core Meta

namespace Destruct

public section

/-- The default structures that are unpacked by `destruct`. -/
def STRUCTURES :=
  #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array].append
  TRANSLATION_STRUCTURES

abbrev DestructM := ReaderT NameSet MetaM

def destructTrivial (t : Expr) (binderName : Name) : DestructM Bijection := do
  let id := Expr.lam binderName t (Expr.bvar 0) .default
  return ⟨id, #[id], .none⟩

mutual
partial def destructAdhoc (t : Expr) (binderName : Name) : DestructM Bijection := do
  if let .some (translated, translation) ← findTranslation t then
    let bij ← destructMain translated binderName
    -- Compute pack as (translation.g ∘ bij.pack)
    -- and unpack as (bij.unpack ∘ translation.f)
    let pack ← lambdaBoundedTelescope bij.pack bij.unpack.size fun fvars packed => do
      let g := Expr.proj ``Translation 1 translation
      mkLambdaFVars fvars (Expr.app g packed)
    let unpack ← bij.unpack.mapM fun un => do
      withLocalDecl binderName .default t fun fvar => do
        let f := Expr.proj ``Translation 0 translation
        mkLambdaFVars #[fvar] (apply un (Expr.app f fvar))
    return ⟨pack, unpack, .none⟩
  destructTrivial t binderName

partial def destructStruct (t : Expr) (binderName : Name)
  (structName : Name) (numFields : Nat) (builtinCtor : Expr) : DestructM Bijection := do
  lambdaBoundedTelescope builtinCtor numFields fun fvars packed => do
    let lctx ← getLCtx
    let fvarInfo := fvars.map fun fvar => lctx.get! fvar.fvarId!
    let types := fvarInfo.map (·.type)
    let names := fvarInfo.map (binderName.toString ++ "_" ++ ·.userName.toString)
    let bijs ← (types.zip names).mapM fun (type, name) => destructMain type name.toName

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

    return ⟨pack, unpack, .none⟩

-- TODO: Update calls to separatePi throughout the codebase?
partial def destructPi (t : Expr) (binderName : Name)
  (inputName : Name) (inputType : Expr) (outputType : Expr) (inputInfo : BinderInfo) : DestructM Bijection := do
  let input ← destructMain inputType inputName
  lambdaBoundedTelescope input.pack input.unpack.size fun vars packed => do
    -- TODO: Is binderName the correct thing to put here? (I think not)
    let output ← destructMain (outputType.instantiate1 packed) binderName

    let unpack ← withLocalDecl binderName .default t fun f => do
      output.unpack.mapM fun field => mkLambdaFVars (#[f] ++ vars) (apply field (f.app packed))

    let types := (lambdaBinders output.pack output.unpack.size).toArray.map fun (name, type) =>
      (name, .default, fun fs => do mkForallFVars vars (type.instantiate (fs.map fun f => mkAppN f vars)))

    withLocalDecls types fun fs => do
      let body := applyN output.pack (fs.map (mkAppN · vars))
      withLocalDecl inputName inputInfo inputType fun var => do
        let replaced := body.replaceFVars vars (input.unpack.map (apply · var))
        let pack ← mkLambdaFVars (fs.push var) replaced
        return ⟨pack, unpack, input.unpack.size::(output.arities.getD [])⟩

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

  destructAdhoc t binderName

partial def destructMain (t : Expr) (binderName : Name) : DestructM Bijection := do
  -- TODO: is this the right thing to do? It's quite often that `t` will be of the
  -- form `(fun x => f x) y`. Consider a case like `∃ (x : X), f x`, which is
  -- really `Exists X (fun x => f x)`. When we destruct this, it'll look like
  -- `{ value : X, proof : (fun x => f x) value }`, and it won't get destructed.
  -- We really would like to see the head symbol `f`. Of course, `whnf` is too
  -- much, but maybe `headBeta` is okay?
  let t := t.headBeta
  if t.isForall then
    destructPi t binderName t.bindingName! t.bindingDomain! t.bindingBody! t.bindingInfo!
  else if t.isConst || t.isApp then
    destructApp t binderName t.getAppFn t.getAppArgs
  else
    destructTrivial t binderName
end

-- Interfaces
partial def destructTactic (goal : MVarId) (premises : Array Name) : MetaM (Array (Array FVarId × MVarId)) := do
  let toRevert ← goal.withContext do
    let mut toRevert := #[]
    let instances ←  (← getLCtx).getFVarIds.filterM fun name => do pure (← name.getBinderInfo).isInstImplicit
    for fvarId in (← getLCtx).getFVarIds do
      unless (← fvarId.getDecl).isAuxDecl || (← instances.anyM fun inst => do localDeclDependsOn (← inst.getDecl) fvarId) || (instances.contains fvarId) do
        toRevert := toRevert.push fvarId
    pure toRevert
  let (_, reverted) ← goal.revert toRevert
  reverted.withContext do
    let bij ← (destructMain (← reverted.getType) `destruct).run (NameSet.ofArray premises)
    -- Note: lambdaMetaTelescope doesn't preserve names, so we have to add back
    -- the names
    let binderNames := ((lambdaBinders bij.pack bij.unpack.size).map (·.1)).toArray
    let (mvars, _, goalBody) ← lambdaMetaTelescope bij.pack bij.unpack.size
    reverted.assign goalBody
    (mvars.zip binderNames).mapM fun (mvar, name) => do
      let arities := bij.arities.getD []
      mvar.mvarId!.setUserName name
      mvar.mvarId!.introNP (arities.take toRevert.size).sum

def destructCanonical (goal : MVarId) (names : Array Name) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  let env ← getEnv
  let consts ← (← goal.getRelevantConstants).toArray.filterMapM getStruct
  let consts ← consts.filterM fun name => do pure !isClass env name
  let goal := (← mkFreshExprMVar (← goal.getType)).mvarId!
  goal.withContext do
    let typ ← goal.getType
    -- let level ← getLevel typ
    let dneg := (env.find? ``Canonical.dneg).get!.value!
    let next := (← goal.apply (Canonical.apply dneg [typ]))[0]!
    let destruct ← destructTactic next (STRUCTURES ++ names ++ consts)
    let result := destruct[0]!
    let ⟨_, _, assignment⟩ := ← abstractMVars
      (← instantiateMVars (← getExprMVarAssignment? goal).get!)
    let assignment ← betaReduce assignment
    return (result.2, fun x => do
      betaReduce (Canonical.apply assignment [← mkLambdaFVars (result.1.map .fvar) x]))

/--
TODO:
-> Obtain fun examples for paper? Was trying to get a problem solved that uses
  destruct very heavily
  Examples (motivation: destruct is needed because otherwise you could blow up search space
  (A and B).left, pairs etc. don't really matter for solving the problem
  anyway):
  - https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Canonical/near/538228811
  - https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/Destruct.20Tactic/near/538032110
-/

structure Bundle (X : Type) (p : X → Prop) where
  value : X
  proof : p value

-- #eval show MetaM Unit from ReaderT.run ((do
--   -- Unit -> Nat -> Nat
--   -- let t := Expr.forallE `n (Expr.const `Unit []) (Expr.forallE `m (Expr.const `Nat []) (Expr.const `Nat []) .default) .default
--
--   -- let t := Expr.forallE `n (Expr.const `Nat []) (Expr.const `Nat []) .default
--
--   -- let t := Expr.forallE `p p (mkAppN (Expr.const `Exists [1]) #[Expr.const `Nat [], Expr.bvar 0]) .default
--
--   let prod2 := mkAppN (Expr.const `Prod [0, 0]) #[mkConst `Nat, mkConst `Nat]
--   let prod3 := mkAppN (Expr.const `Prod [0, 0]) #[prod2, mkConst `Nat]
--   let t := Expr.forallE `x prod2 (Expr.forallE `y prod3 (mkConst `Nat) .default) .default
--
--   -- (X : Type) → Bundle X (fun (x : X) → x = x)
--   -- let t := Expr.forallE `X (Expr.sort 1) (mkAppN (Expr.const ``Bundle []) #[Expr.bvar 0, Expr.lam `x (Expr.bvar 0) (mkAppN (Expr.const `Eq [1]) #[Expr.bvar 1, Expr.bvar 0, Expr.bvar 0]) .default]) .default
--
--   -- ∀ n : Nat, n * n = 1 ↔ n = 1
--   -- let t ← inferType (Expr.const ``example_theorem [])
--   let b ← destructMain t `x
--   IO.println $ ← b.pp
--   IO.println $ ← check b.pack
--   IO.println $ ← b.unpack.mapM (fun e => do check e)
-- ) : DestructM Unit) (NameSet.ofArray #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array])
