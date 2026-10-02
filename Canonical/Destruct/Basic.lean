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

structure Context where
  /-- The structures that are unpacked by `destruct`. -/
  structures : NameSet
  /-- The translations `destruct` will attempt to apply to subexpressions. -/
  translations : Array MetaTranslation

def STRUCTURES : Array Name := #[``Prod, ``PProd, ``And, ``Sigma, ``PSigma, ``Iff, ``MProd, ``Subtype, ``Fin, ``Array, ``Unit']
def TRANSLATIONS : Array Name := #[``translate_exists, ``translate_true, ``translate_unit, ``translate_punit]

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

-- Returns the replaced expression as well as the Translation.
def matchTranslation (t : Expr) : DestructM (Option (Expr × Expr × Expr)) := withTransparency .none do
  for mt in (← read).translations do
    let levels ← mkFreshLevelMVars mt.levels.length
    let type := mt.type.instantiateLevelParams mt.levels levels
    let (mvars, _, translation) ← forallMetaTelescope type
    let pattern := translation.getAppArgs[0]!
    let replace := translation.getAppArgs[1]!
    if ← isDefEqGuarded t pattern then
      let replaced ← instantiateMVars replace
      let f := mt.f.instantiateLevelParams mt.levels levels
      let f ← instantiateMVars (applyN f mvars)
      let g := mt.g.instantiateLevelParams mt.levels levels
      let g ← instantiateMVars (applyN g mvars)
      return .some (replaced, f, g)
  return .none

mutual
partial def destructFVar (fvar : Expr) (binderName : Name) : DestructM Bijection := do
  let lctx ← getLCtx
  let info := lctx.get! fvar.fvarId!
  let name := prefixName binderName info.userName
  destructMain info.type name

partial def destructStruct (t : Expr) (binderName : Name)
  (structName : Name) (numFields : Nat) (builtinCtor : Expr) : DestructM Bijection := do
  lambdaBoundedTelescope builtinCtor numFields fun fvars packed => do
    let bijs ← fvars.mapM (destructFVar · binderName)

    let pack ← packTelescope (bijs.zip fvars).toList fun vars packeds => do
      mkLambdaFVars vars (packed.replaceFVars fvars packeds)

    let unpack ← withLocalDecl binderName .default t fun fvar => do
      let projs := Array.ofFn (n := numFields) (.proj structName · fvar)
      let unpacks ← (bijs.zip projs).mapM fun (b, proj) => do
        b.unpack.mapM fun lam => do
          mkLambdaFVars #[fvar] (apply (lam.replaceFVars fvars projs) proj)
      return unpacks.flatten

    return { pack, unpack, madeProgress := true }

partial def destructPi (t : Expr) (binderName : Name)
  (inputName : Name) (inputType : Expr) (outputType : Expr) (inputInfo : BinderInfo) : DestructM Bijection := do
  let input ← destructMain inputType inputName
  lambdaBoundedTelescope input.pack input.unpack.size fun vars packed => do
    -- TODO: Is binderName the correct thing to put here?
    let output ← destructMain (outputType.instantiate1 packed) binderName

    let unpack ← withLocalDecl binderName .default t fun f => do
      output.unpack.mapM fun field => mkLambdaFVars (#[f] ++ vars) (apply field (f.app packed))

    let pack ← lambdaBoundedTelescopeDestruct output.pack output.unpack.size vars fun fs body => do
      withLocalDecl inputName inputInfo inputType fun var => do
        let replaced := body.replaceFVars vars (input.unpack.map (apply · var))
        mkLambdaFVars (fs.push var) replaced

    return { pack, unpack, arities := input.unpack.size :: output.arities, madeProgress := input.madeProgress || output.madeProgress }

partial def destructTranslation (t : Expr) (binderName : Name) : DestructM Bijection := do
  let .some (translated, f, g) ← matchTranslation t | return destructTrivial t binderName
  let bij ← destructMain translated binderName
  let pack ← lambdaBoundedTelescope bij.pack bij.unpack.size fun fvars packed => do
    mkLambdaFVars fvars (apply g packed)
  let unpack ← bij.unpack.mapM fun un => withLocalDecl binderName .default t fun fvar => do
    mkLambdaFVars #[fvar] (apply un (apply f fvar))
  return { pack, unpack, madeProgress := true }

partial def destructApp (t : Expr) (binderName : Name) (headFn : Expr) (headArgs : Array Expr) : DestructM Bijection := do
  if headFn.constName?.isNone then return destructTrivial t binderName
  let headName := headFn.constName!
  let env ← getEnv

  if (← read).structures.contains headName then
    if let .some info := getStructureInfo? env headName then
      let induct ← getConstInfoInduct headName
      if induct.isRec then return destructTrivial t binderName
      let ctor ← etaExpand (.const induct.ctors[0]! headFn.constLevels!)
      return ← destructStruct t binderName headName info.fieldNames.size (applyN ctor headArgs)

  destructTranslation t binderName

partial def destructMain (t : Expr) (binderName : Name) : DestructM Bijection := do
  match (← whnf t.consumeMData) with
  | t@(.forallE name type body info) => destructPi t binderName name type body info
  | t@(.const _ _) | t@(.app _ _) => destructApp t binderName t.getAppFn t.getAppArgs
  | _ => return destructTrivial t binderName
end

-- Interfaces
partial def destructTactic (goal : MVarId) (context : Context) : MetaM (Array (Array FVarId × MVarId) × Bool) := do
  -- TODO: Potentially refactor this? We can maybe think about putting the
  -- return type in a struct
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
    let binderNames := ((lambdaBinders bij.pack bij.unpack.size).map (·.1)).toArray
    let (mvars, _, goalBody) ← lambdaMetaTelescope bij.pack bij.unpack.size
    reverted.assign goalBody
    let goalInfo ← (mvars.zip binderNames).mapM fun (mvar, name) => do
      mvar.mvarId!.setUserName name
      mvar.mvarId!.introNP (bij.arities.take toRevert.size).sum
    return (goalInfo, bij.madeProgress)

def destructCanonical (goal : MVarId) (names : Array Name) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  let env ← getEnv
  let consts ← (← goal.getRelevantConstants).toArray.filterMapM getStruct
  let consts ← consts.filterM fun name => do pure !isClass env name
  let goal := (← mkFreshExprMVar (← goal.getType)).mvarId!
  goal.withContext do
    let typ ← goal.getType
    let dneg := (env.find? ``Canonical.dneg).get!.value!
    let next := (← goal.apply (Canonical.apply dneg [typ]))[0]!
    let context ← Context.populate (names ++ consts)
    let destruct ← destructTactic next context
    let destruct := destruct.1
    let result := destruct[0]!
    let ⟨_, _, assignment⟩ := ← abstractMVars
      (← instantiateMVars (← getExprMVarAssignment? goal).get!)
    let assignment ← betaReduce assignment
    return (result.2, fun x => do
      betaReduce (Canonical.apply assignment [← mkLambdaFVars (result.1.map .fvar) x]))
