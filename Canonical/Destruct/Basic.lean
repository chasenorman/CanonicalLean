module

import Lean
import Canonical.Util
import Canonical.Symbols
public import Canonical.Destruct.Translation

open Lean Core Meta

namespace Destruct

public section

/-- A structure storing the constant information for the `destruct` tactic. -/
structure Context where
  /-- The structures that are unpacked by `destruct`. -/
  structures : NameSet
  /-- The translations `destruct` will attempt to apply to subexpressions. -/
  translations : Array MetaTranslation

/-- Default structures that `destruct` will unpack. -/
def STRUCTURES : Array Name := #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array, ``Unit', ``Inhabited]
/-- Default translations that `destruct` will apply. -/
def TRANSLATIONS : Array Name := #[``translate_exists, ``translate_nonempty, ``translate_true, ``translate_unit, ``translate_punit]

def Context.populate (names : Array Name) : MetaM Context := do
  let names := TRANSLATIONS ++ names
  let mut structures : NameSet := NameSet.ofArray STRUCTURES
  let mut translations := #[]
  let env ← getEnv
  for name in names do
    if let .some _ := getStructureInfo? env name then
      structures := structures.insert name
    else if let .some info := env.find? name then
      if let .some mt ← (MetaTranslation.make info).run then
        translations := translations.push mt
  return { structures, translations }

def destructTrivial (t : Expr) (binderName : Name) : Bijection :=
  let id := .lam binderName t (.bvar 0) .default
  { pack := id, unpack := #[id] }

abbrev DestructM := ReaderT Context MetaM

def matchTranslation (t : Expr) : DestructM (Option (Expr × Expr × Expr)) := withTransparency .none do
  for mt in (← read).translations do
    let levels ← mkFreshLevelMVars mt.levels.length
    let type := mt.type.instantiateLevelParams mt.levels levels
    let (mvars, _, translation) ← forallMetaTelescope type
    if ← isDefEqGuarded t (translation.getAppArgs[0]!) then
      let replaced ← instantiateMVars (translation.getAppArgs[1]!)
      let f := mt.f.instantiateLevelParams mt.levels levels
      let f ← instantiateMVars (applyN f mvars)
      let g := mt.g.instantiateLevelParams mt.levels levels
      let g ← instantiateMVars (applyN g mvars)
      return .some (replaced, f, g)
  return .none

mutual
partial def destructFVar (fvar : Expr) (binderName : Name) : DestructM Bijection := do
  let info := (← getLCtx).get! fvar.fvarId!
  let name := prefixName binderName info.userName
  destructMain info.type name

partial def destructStruct (t : Expr) (binderName : Name)
  (structName : Name) (numFields : Nat) (builtinCtor : Expr) : DestructM Bijection := do
  lambdaBoundedTelescope builtinCtor numFields fun fvars packed => do
    let bijs ← fvars.mapM (destructFVar · binderName)

    let pack ← packTelescope (bijs.zip fvars).toList fun vars packs => do
      mkLambdaFVars vars (packed.replaceFVars fvars packs)

    let unpack ← withLocalDecl binderName .default t fun fvar => do
      let projs := Array.ofFn (n := numFields) (.proj structName · fvar)
      let unpacks ← (bijs.zip projs).mapM fun (b, proj) => do
        b.unpack.mapM fun lam => do
          mkLambdaFVars #[fvar] (apply (lam.replaceFVars fvars projs) proj)
      return unpacks.flatten

    return { pack, unpack, madeProgress := true }

partial def destructPi (t : Expr) (binderName : Name) (inputName : Name) (inputType : Expr)
  (outputType : Expr) (inputInfo : BinderInfo) : DestructM Bijection := do
  let input ← destructMain inputType inputName
  lambdaBoundedTelescope input.pack input.unpack.size fun vars packed => do
  withNewBinderInfos (vars.map (·.fvarId!, inputInfo)) do
    let output ← destructMain (outputType.instantiate1 packed) binderName

    let unpack ← withLocalDecl binderName .default t fun f => do
      output.unpack.mapM fun field => mkLambdaFVars (#[f] ++ vars) (apply field (f.app packed))

    let pack ← lambdaBoundedTelescopeDestruct output.pack output.unpack.size vars fun fs body => do
      withLocalDecl inputName inputInfo inputType fun var => do
        let replaced := body.replaceFVars vars (input.unpack.map (apply · var))
        mkLambdaFVars (fs.push var) replaced

    return { pack, unpack, arities := input.unpack.size :: output.arities,
              madeProgress := input.madeProgress || output.madeProgress }

partial def destructTranslation (t : Expr) (binderName : Name) : DestructM Bijection := do
  let .some (translated, f, g) ← matchTranslation t | return destructTrivial t binderName
  let bij ← destructMain translated binderName
  let pack ← lambdaBoundedTelescope bij.pack bij.unpack.size fun fvars packed => do
    mkLambdaFVars fvars (apply g packed)
  let unpack ← bij.unpack.mapM fun un => withLocalDecl binderName .default t fun fvar => do
    mkLambdaFVars #[fvar] (apply un (apply f fvar))
  return { pack, unpack, madeProgress := true }

partial def destructApp (t : Expr) (binderName : Name) (headFn : Expr) (headArgs : Array Expr) : DestructM Bijection := do
  let .some headName := headFn.constName? | return destructTrivial t binderName
  if (← read).structures.contains headName then
    if let .some info := getStructureInfo? (← getEnv) headName then
      let induct ← getConstInfoInduct headName
      if induct.isRec then return destructTrivial t binderName
      let ctor ← etaExpand (.const induct.ctors[0]! headFn.constLevels!)
      return ← destructStruct t binderName headName info.fieldNames.size (applyN ctor headArgs)

  destructTranslation t binderName

partial def destructMain (t : Expr) (binderName : Name) : DestructM Bijection := do
  match ← whnf t.consumeMData with
  | t@(.forallE name type body info) => destructPi t binderName name type body info
  | t@(.const _ _) | t@(.app _ _) => destructApp t binderName t.getAppFn t.getAppArgs
  | _ => return destructTrivial t binderName
end

def reduceProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .proj _ i s := e | return .done e
    let some r ← projectCore? s.headBeta i | return .done e
    return .visit r)

-- Interfaces
/-- Destructs `goal` into new goals. Also returns whether progress was made, and a map from a proof
    of `goal` to proofs of the new goals (each in the context of its new goal). -/
partial def destructTactic (goal : MVarId) (context : Context) :
    MetaM (Array (Array FVarId × MVarId) × Bool × (Expr → MetaM (Array Expr))) := do
  let toRevert ← goal.withContext do
    let mut toRevert := #[]
    let instances ← (← getLCtx).getFVarIds.filterM fun name => do pure (← name.getBinderInfo).isInstImplicit
    for fvarId in (← getLCtx).getFVarIds do
      unless (← fvarId.getDecl).isAuxDecl || (← instances.anyM fun inst => do localDeclDependsOn (← inst.getDecl) fvarId) || (instances.contains fvarId) do
        toRevert := toRevert.push fvarId
    pure toRevert
  let (_, reverted) ← goal.revert toRevert
  reverted.withContext do
    let bij ← (destructMain (← reverted.getType) `destruct).run context
    -- Note: lambdaMetaTelescope doesn't preserve names, so we have to add back
    -- the names
    let binderNames := lambdaBinderNames bij.pack bij.unpack.size
    let (mvars, _, goalBody) ← lambdaMetaTelescope (← reduceProjs bij.pack) bij.unpack.size
    reverted.assign goalBody
    let goalInfo ← (mvars.zip binderNames).mapM fun (mvar, name) => do
      mvar.mvarId!.setUserName name
      mvar.mvarId!.introNP (bij.arities.take toRevert.size).sum
    let forward proof := do
      let proof ← goal.withContext do mkLambdaFVars (toRevert.map .fvar) proof
      return (bij.unpack.zip goalInfo).map fun (unpack, fvars, _) =>
        applyN (apply unpack proof) (fvars.map .fvar)
    return (goalInfo, bij.madeProgress, forward)

/-- Destructs `goal` into a single new goal. Returns it, together with maps `reconstruct` from a proof
    of the new goal to a proof of `goal`, and `forward` from a proof of `goal` to one of the new goal. -/
def destructCanonical (goal : MVarId) (names : Array Name) :
    MetaM (MVarId × (Expr → MetaM Expr) × (Expr → MetaM Expr)) := do
  let env ← getEnv
  let goal ← goal.withContext do pure (← mkFreshExprMVar (← goal.getType)).mvarId!
  goal.withContext do
    let typ ← goal.getType
    let dneg := (env.find? ``Canonical.dneg).get!.value!
    let next := (← goal.apply (Canonical.apply dneg [typ]))[0]!
    let context ← Context.populate (names.filter (!isClass env ·))
    let destruct ← destructTactic next context
    let result := destruct.1[0]!
    let ⟨_, _, assignment⟩ := ← abstractMVars
      (← instantiateMVars (← getExprMVarAssignment? goal).get!)
    let assignment ← reduceProjs (← betaReduce assignment)
    let reconstruct x := do
      reduceProjs (← betaReduce (Canonical.apply assignment [← mkLambdaFVars (result.1.map .fvar) x]))
    -- `next` has type `(Destruct : STAR (Sort u)) → (typ → Destruct) → Destruct`.
    let forward proof := do
      let dnegProof ← forallBoundedTelescope (← next.getType) (some 2) fun xs _ =>
        mkLambdaFVars xs (.app xs[1]! proof)
      return (← destruct.2.2 dnegProof)[0]!
    return (result.2, reconstruct, forward)
