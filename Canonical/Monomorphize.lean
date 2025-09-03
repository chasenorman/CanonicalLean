import Lean
open Lean Elab Tactic Expr Std
open Meta

namespace Monomorphize

@[inline]
def Std.TreeSet.subset (t₁ t₂ : TreeSet α cmp) : Bool :=
  t₁.all (t₂.contains ·)

abbrev NameSet.subset : NameSet -> NameSet -> Bool := Std.TreeSet.subset

/-- An expression with `levels` as `param` universes. -/
structure UnivAbstracted where
  expr: Expr
  levels: List Name

/-- UnivAbstracted are equal up to renaming of `levels`. -/
instance : BEq UnivAbstracted where
  beq := fun x y =>
    if x.levels.length != y.levels.length then false else
    let levels := y.levels.map Level.param
    y.expr == (instantiateLevelParams x.expr x.levels levels)

/-- Uses the hashing for `Expr` with a canonical instantiation of `levels`. -/
instance : Hashable UnivAbstracted where
  hash := fun x => (instantiateLevelParams x.expr x.levels (x.levels.map (fun _ => Level.zero))).hash

/-- A metavariable and its future intended assignment, to serve as a new symbol during pre-processing. -/
structure MetaAbstraction where
  id: MVarId
  assignment: UnivAbstracted

/-- State monad for monomorphization -/
structure MonoState where
  /-- A mapping from symbols (consts, fvars, mvars) to their monomorphizations. -/
  mono: HashMap Expr (List MetaAbstraction) := .emptyWithCapacity 8
  /-- Types of instances relevant to the problem. -/
  candidateInsts: HashSet UnivAbstracted := .emptyWithCapacity 8
  /-- FVars that are safe to be used in the definition of monomorphizations. -/
  globalFVars: HashSet FVarId := .emptyWithCapacity 0
  /-- Names of all constants we encounter. -/
  constNames: NameSet := .empty
  /-- "Dirty" flag for `constNames`. -/
  hasNewConst: Bool := true

instance : ToString MonoState where
  toString s := s!"{s.mono.toList.map fun x => x.1}\n{s.candidateInsts.toList.map fun x => x.expr}"

abbrev MonoM := StateRefT MonoState MetaM

/-- Add `name` to `constNames`. -/
def addConstant (name : Name) : MonoM Unit := do
  modify fun s => { s with
    constNames := s.constNames.insert name,
    hasNewConst:= s.hasNewConst || !s.constNames.contains name
  }

/-- Add `names` to `constNames`. -/
def addConstants (names : NameSet) : MonoM Unit := do
  modify fun s => { s with
    constNames := Union.union s.constNames names,
    hasNewConst := s.hasNewConst || !(NameSet.subset names s.constNames)
  }

def getConstants : MonoM NameSet := do
  return (← get).constNames

/-- If `id` is instImplicit, add its type to `candidateInsts`. -/
def addFVarAsCandidate (id : FVarId) : MonoM Unit := do
  assert! (← id.getBinderInfo).isInstImplicit
  if (← get).globalFVars.contains id then
    let type ← id.getType
    modify fun s => { s with candidateInsts := s.candidateInsts.insert ⟨type, []⟩ }

/-- Set `hasNewConst` to `false` and return the previous value. -/
def consumeNewConstFlag : MonoM Bool := do
  let s ← get
  modify fun s => { s with hasNewConst := false }
  return s.hasNewConst

/-- Collect the `binderInfos` of the `forallE` telescope. -/
partial def getAllBinderInfos (e : Expr) : MetaM (List BinderInfo) := do
  match e with
  | forallE _ _ b i         => return i :: (← getAllBinderInfos b)
  | mdata _ b | lam _ _ b _ | app _ b | letE _ _ _ b _ => getAllBinderInfos b
  --No other cases can potentially contain foralls. --
  | _                       => return []

/-- `updateForallBinderInfos` for lambda expressions. -/
def updateLambdaBinderInfos (e : Expr) (binderInfos? : List (Option BinderInfo)) : Expr :=
  match e, binderInfos? with
  | Expr.lam binderName binderType body binderInfo, newBi? :: binderInfos? =>
    /-recursively also update the body. -/
    let body  := updateLambdaBinderInfos body binderInfos?
    let binderInfo := newBi?.getD binderInfo
    Expr.lam binderName binderType body binderInfo
  | e, _ => e

/-- Takes an expression and outputs the head symbol, type, and level parameters. -/
def getHeadInfo : Expr → MetaM (Option (Expr × Expr × List Name))
| e@(fvar id) | e@(mvar id) => return some (e, ← id.getType, [])
| const name us => do
  let info := ((← getEnv).find? name).get!
  -- Levels set to .zero for all constants to create the canonical version for comparison.
  return some (.const name (us.map fun _ => Level.zero), info.type, info.levelParams)
| _ => return none

/-- Outputs the name of a head symbol. -/
def toName : Expr → MetaM Name
| .fvar id => return id.name.updatePrefix (← id.getUserName).getRoot
| .mvar id => return id.name.updatePrefix ((← getMCtx).getDecl id).userName
| .const name _ => return name
| e => panic! s!"toName applied to non-head symbol: {e}"

/-- Checks if all free variables in `e` are in `globalFVars`. -/
def onlyHasGlobalFVars (e : Expr) : MonoM Bool := do
  let globalFVars := (← get).globalFVars
  let p := fun x => !globalFVars.contains x
  return !e.hasAnyFVar p

/-- Add a typeclass instance to `candidateInsts`. -/
partial def addAsCandidate (inst : Expr) : MonoM Unit := do
  if ← onlyHasGlobalFVars inst then
    let ⟨levels, _, type⟩ ← abstractMVars (← inferType inst)
    modify fun inst => { inst with candidateInsts := inst.candidateInsts.insert ⟨type, levels.toList⟩ }

/-- Unfolds constants that are not global instances at the head of `e`.  -/
partial def unfoldInstDefn (e : Expr) : MetaM Expr := do
  let (name, args) := getAppFnArgs e
  let env ← getEnv
  if let some info := env.find? name then
    if !isGlobalInstance env name then
      if let some value := info.value? then
        return ← unfoldInstDefn (← whnfR (mkAppN value args))
  return e

/-- Apply `transform` to the type and local context of `goal`. -/
def transformMVar [Monad n] [MonadLiftT MetaM n] [MonadMCtx n] (goal : MVarId) (transform : Expr → n Expr) : n (Expr × LocalContext) := do
  let decl := ((← getMCtx).findDecl? goal).get!
  let type ← transform decl.type

  let lctx := { decl.lctx with decls := ← decl.lctx.decls.mapM fun decl => do decl.mapM fun decl => do
    let decl := decl.setType (← transform decl.type)

    if let some value := decl.value? then
      pure (decl.setValue (← transform value))
    else pure decl
  }

  return (type, lctx)

/-- Abstract all non-instImplicit subterms in `e` into metavaraibles.
    Add all instImplicit subterms as candidate instances. -/
partial def monoPattern (e : Expr) : MonoM (Option Expr) := do
  withApp e fun fn args => do
    if let some (_, type, levels) ← getHeadInfo fn then
      -- Assign new metavariable levels so outputs are independent of levels.
      let mvarlevels ← mkFreshLevelMVars levels.length
      let fn := fn.instantiateLevelParams levels mvarlevels
      let (metas, binders, _) ← forallMetaTelescopeReducing
        (type.instantiateLevelParams levels mvarlevels)
      -- Check that `e` is eta expanded.
      if metas.size != args.size then return none
      for i in [0:binders.size] do
        if binders[i]!.isInstImplicit then
          if let some childPattern ← monoPattern (← unfoldInstDefn args[i]!) then
            let _ ← addAsCandidate childPattern
            -- Assign metas[i] to the child pattern.
            let success ← isDefEq metas[i]! childPattern
            assert! success
            if !success then
              logWarning s!"Monomorphization failure: {e}"
              return none
          else return none
      return ← instantiateMVars (mkAppN fn metas)
    else return none

/-- Monomorphizes the head of `e`, creating a new monomorphization metavariable if necessary. -/
partial def monoTransformStep (e : Expr) : MonoM TransformStep := do
  withApp e fun fn _ => do
    if let some (fn, type, _) ← getHeadInfo fn then
      let hasInstImplicit ← forallTelescopeReducing type fun xs _ =>
        do xs.anyM fun x => do pure (← x.fvarId!.getBinderInfo).isInstImplicit
      if hasInstImplicit then
        -- Check if we can use a pre-existing monomorphization.
        let cachedSpec := (← get).mono.getD fn []
        for ⟨specmVar, ⟨specBody, specLevels⟩⟩ in cachedSpec do
          let mvarlevels ← mkFreshLevelMVars specLevels.length
          let instantiated := specBody.instantiateLevelParams specLevels mvarlevels
          let ⟨metas, _, body⟩ ← lambdaMetaTelescope instantiated
          if ← isDefEqGuarded e body then
            let newExpr ← pure (mkAppN (.mvar specmVar) (← metas.mapM instantiateMVars))
            return .continue newExpr

        -- Otherwise, create a monomorphization.
        if let some monoPattern ← monoPattern e then
          if ← onlyHasGlobalFVars monoPattern then
            let monoPattern ← instantiateMVars monoPattern
            let ⟨paramNames, mvars, abstracted⟩ ← abstractMVars monoPattern
            let specName := Name.mkSimple (((← toName fn).num cachedSpec.length).toStringWithSep "_" true)
            let specMvarId := (← mkFreshExprMVar (← inferType
              (abstracted.instantiateLevelParams paramNames.toList (← mkFreshLevelMVars paramNames.size))) .syntheticOpaque specName).mvarId!
            -- Add this to mono state.
            modify fun s => { s with
              mono := s.mono.insert fn (⟨specMvarId, ⟨abstracted, paramNames.toList⟩⟩ :: cachedSpec)
            }
            let _ ← addConstants monoPattern.getUsedConstantsAsSet
            let success ← isDefEq monoPattern e
            if !success then
              logWarning s!"Failed to monomorphize {fn}"
              return .continue

            let newExpr ← instantiateMVars (mkAppN (.mvar specMvarId) mvars)
            return .continue newExpr
    return .continue

def preprocessMono (e : Expr) : MonoM Expr := do
  match ← monoTransformStep e with
  | .done e | .visit e | .continue (some e) | _ => return e

/-- Perform the assignments given by the `MetaAbstractions` in `mono`. -/
def finalizeMonos : MonoM Unit := do
  (← get).mono.values.flatten.forM fun mono =>
    do if !(← mono.id.isAssigned) then
        mono.id.assign mono.assignment.expr

/-- Get the types of all instImplicit subterms in `e`. -/
partial def getInstanceTypes (e : Expr) : MetaM (HashSet Expr) := do
  match e with
  | app _ _ =>
      let (fn, args) := Expr.getAppFnArgs e
      if let some info := (← getEnv).find? fn then
        let bs ← getAllBinderInfos info.type
        let insts ← (bs.toArray.zip args).filterMapM fun ⟨binfo, arg⟩ => do
          if !binfo.isInstImplicit || arg.hasLooseBVars then
            return none
          else some <$> inferType arg
          -- Recursively check all arguments.
        args.foldlM (fun acc a => return acc ∪ (← getInstanceTypes a)) (HashSet.ofArray insts)
      else
        return ∅
  | mdata _ b | lam _ _ b _ | letE _ _ _ b _ => getInstanceTypes b
  | _ => return ∅

/-- Find all possible ways to unify each element in `todo` with elements of `candidates`, and accumulate the result of `cb` on each. -/
partial def unifyWithCand (todo : List Expr) (candidates : List UnivAbstracted) (cb : MonoM (Option Expr)) : MonoM (List Expr) := do
  match todo with
  | [] => return (← cb).toList
  | type :: todo =>
    let type ← instantiateMVars type
    -- If there is unification to be done,
    if type.hasMVar then
      -- For each candidate instance,
      let branches ← candidates.filterMapM fun (inst : UnivAbstracted) => do
        withoutModifyingMCtx do -- fork the MCtx to consider each branch independently
          -- Abstract over lambda bindings and universe levels.
          let (_, _, inst) ← lambdaMetaTelescope
            (inst.expr.instantiateLevelParams inst.levels (← mkFreshLevelMVars inst.levels.length))
          if ← isDefEqGuarded type inst then
            -- continue unifying the remainder of `todo`.
            return some (← unifyWithCand todo candidates cb)
          else return none
      if !branches.isEmpty then
        return branches.flatten
    -- If there is no unification, we continue anyway.
    unifyWithCand todo candidates cb

/-- Generates all monomorphizations for a given constant. -/
def monomorphizeConst (name : Name) : MonoM (List Expr) := do
  -- First, get the instance implicit arguments of the constant.
  let constInfo ← getConstInfo name

  let levels ← constInfo.levelParams.mapM fun _ => mkFreshLevelMVar

  let typeInstantiated := constInfo.type.instantiateLevelParams constInfo.levelParams levels

  -- Turn foralls to metavariables to solve.
  let (mvars, binders, body) ← forallMetaTelescopeReducing typeInstantiated

  let instImplicit := (mvars.zip binders).filterMap fun ⟨m, binfo⟩ =>
    if binfo.isInstImplicit then some m else none

  -- Filter for instImplicit arguments and put them into todo list.
  let instImplicitTypes ← instImplicit.mapM fun mvar => do mvar.mvarId!.getType
  let todo := (← getInstanceTypes body).insertMany instImplicitTypes.toList

  unifyWithCand todo.toList (← get).candidateInsts.toList do
    for mvar in instImplicit do
      let mty ← instantiateMVars (← mvar.mvarId!.getType)
      match ← trySynthInstance mty with
      | .some inst => do
        let success ← isDefEq mvar inst
        assert! success
      | .none => return none
      | .undef => pure ()

    let appliedExpr := mkAppN (Expr.const name levels) mvars
    let instantiated ← instantiateMVars appliedExpr
    let abstrResult ← abstractMVars instantiated
    let binfos := abstrResult.mvars.map fun mvar =>
      (mvars.idxOf? mvar).map fun idx => binders[idx]!

    -- Check if this constant already has this monomorphization.
    let result := updateLambdaBinderInfos abstrResult.expr binfos.toList
    let set := (← get).mono.getD (Expr.const name (levels.map fun _ => Level.zero)) []
    for mono in set do
      let sameLevels := mono.assignment.expr.instantiateLevelParams mono.assignment.levels (abstrResult.paramNames.toList.map Level.param)
      if sameLevels == result then
        return none

    -- The proper thing to do is to return the levels, too.
    let result := result.instantiateLevelParams abstrResult.paramNames.toList (abstrResult.paramNames.toList.map (fun _ => Level.zero))

    let _ ← addConstants result.getUsedConstantsAsSet

    return result

structure MonoConfig where
  canonicalize : Bool := true

declare_config_elab monoConfig MonoConfig

def monomorphizeTactic (goal : MVarId) (ids : Array Syntax) (config : MonoConfig) : MonoM MVarId := do
  -- Consider instImplicit local decls.
  for decl in ((← getMCtx).findDecl? goal).get!.lctx.decls do
    if let some decl := decl then
      if decl.binderInfo.isInstImplicit then
        addFVarAsCandidate decl.fvarId

  -- First pass: collect `candidateInsts` and ignore the transformation result.
  let _ ← transformMVar goal fun e => Meta.transform e (pre := monoTransformStep)

  -- Process premises by creating all monomorphized versions.
  -- Name is the new name we create and expr is the monomorphized instance.
  let consts ← ids.mapM resolveGlobalConstNoOverload
  -- We don't foldlM immediately because we need the index.
  let exprs : List (Name × Expr) ← consts.toList.flatMapM fun const => do
    let results ← monomorphizeConst const
    return results.mapIdx fun idx expr =>
      let name := Name.mkSimple ((const.num idx).toStringWithSep "_" true)
      (name, expr)

  -- Add the newly generated monomoprhizations into the context.
  let goal ← exprs.foldlM (fun goal (name, result) => do
    pure (← MVarId.note goal name result).2
  ) goal

  -- Canonicalize by noting the `monos`.
  if config.canonicalize then
    let goal ← (← get).mono.toList.foldlM (fun goal pair => do
      let (_, monos) := pair
      monos.foldlM (fun goal mono => do
        -- Assign the metavariable to a new local decl which is assigned to the monomorphization.
        let name := ((← getMCtx).getDecl mono.id).userName
        let noteResult ← MVarId.note goal name (mono.assignment.expr.instantiateLevelParams mono.assignment.levels (mono.assignment.levels.map (fun _ => Level.zero)))
        mono.id.assign (.fvar noteResult.1)
        pure noteResult.2
      ) goal
    ) goal

    -- The second pass substitutes the `monos`.
    let (type, lctx) ← transformMVar goal fun e => Meta.transform e (pre := monoTransformStep)
    -- Failsafe for new `monos` being added during the second pass.
    let _ ← finalizeMonos
    let _ ← goal.modifyLCtx fun _ => lctx
    goal.replaceTargetDefEq type
  else return goal

syntax (name := monomorphize) "monomorphize " Parser.Tactic.optConfig ("[" ident,* "]")? : tactic

@[tactic monomorphize] def evalMonomorphize : Tactic
| `(tactic| monomorphize $config [$ids:ident,*]) => do
  let config ← monoConfig config
  liftMetaTactic1 fun goal =>
    goal.withContext do
      (monomorphizeTactic goal ids.getElems config).run' { globalFVars := HashSet.ofArray (← getLCtx).getFVarIds }
| `(tactic| monomorphize $config) => do
  let config ← monoConfig config
  liftMetaTactic1 fun goal =>
    goal.withContext do
      (monomorphizeTactic goal #[] config).run' { globalFVars := HashSet.ofArray (← getLCtx).getFVarIds }
| _ => throwUnsupportedSyntax
