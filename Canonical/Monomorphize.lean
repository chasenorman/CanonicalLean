import Lean
open Lean Elab Tactic Expr Std
open Meta hiding transform

namespace Monomorphize

structure Abstracted where
  expr : Expr
  levels : List Name

instance : BEq Abstracted where
  beq := fun x y =>
    if x.levels.length != y.levels.length then false else
    let levels := y.levels.map Level.param
    y.expr == (instantiateLevelParams x.expr x.levels levels)

instance : Hashable Abstracted where
  hash := fun x => (instantiateLevelParams x.expr x.levels (x.levels.map (fun _ => Level.zero))).hash

structure Mono where
  id: MVarId
  levels: List Name
  assignment: Expr

structure MonoState where
  mono: HashMap Expr (List Mono) := .emptyWithCapacity 8
  given: HashSet Abstracted := .emptyWithCapacity 8
  globalFVars: HashSet FVarId := .emptyWithCapacity 0
  constants: NameSet := .empty
  dirty: Bool := true

instance : ToString MonoState where
  toString s := s!"{s.mono.toList.map fun x => x.1}\n{s.given.toList.map fun x => x.expr}"

abbrev MonoM := StateRefT MonoState MetaM

def addConstant (name : Name) : MonoM Unit := do
  modify fun s => { s with
    constants := s.constants.insert name,
    dirty := s.dirty || !s.constants.contains name
  }

def addConstants (names : NameSet) : MonoM Unit := do
  modify fun s => { s with
    constants := s.constants.union names,
    dirty := s.dirty || !names.subset s.constants
  }

def getConstants : MonoM NameSet := do
  return (← get).constants

def registerPremise (id : FVarId) : MonoM Unit := do
  assert! (← id.getBinderInfo).isInstImplicit
  if (← get).globalFVars.contains id then
    let type ← id.getType
    modify fun s => { s with given := s.given.insert ⟨type, []⟩}

def consumeDirty : MonoM Bool := do
  let s ← get
  modify fun s => { s with dirty := false }
  return s.dirty

partial def getBinders (e : Expr) : MetaM (List BinderInfo) := do
  match e with
  | forallE _ _ b i        => return i :: (← getBinders b)
  | mdata _ b | lam _ _ b _ | app _ b | letE _ _ _ b _ => getBinders b
  | _                      => return []

def updateLambdaBinderInfos (e : Expr) (binderInfos? : List (Option BinderInfo)) : Expr :=
  match e, binderInfos? with
  | Expr.lam n d b bi, newBi? :: binderInfos? =>
    let b  := updateLambdaBinderInfos b binderInfos?
    let bi := newBi?.getD bi
    Expr.lam n d b bi
  | e, _ => e

def asHead : Expr → MetaM (Option (Expr × Expr × List Name))
| e@(fvar id) | e@(mvar id) => return some (e, ← id.getType, [])
| const name us => do
  let info := ((← getEnv).find? name).get!
  return some (.const name (us.map fun _ => Level.zero), info.type, info.levelParams)
| _ => return none

def toName : Expr → MetaM Name
| .fvar id => return id.name.updatePrefix (← id.getUserName).getRoot
| .mvar id => return id.name.updatePrefix ((← getMCtx).getDecl id).userName
| .const name _ => return name
| e => panic! s!"toName applied to non-head symbol: {e}"

def onlyGlobalFVars (e : Expr) : MonoM Bool := do
  let globalFVars := (← get).globalFVars
  let p := fun x => !globalFVars.contains x
  return !e.hasAnyFVar p

partial def registerInstance (s : Expr) : MonoM Unit := do
  if ← onlyGlobalFVars s then
    let ⟨levels, _, type⟩ ← abstractMVars (← inferType s)
    modify fun s => { s with given := s.given.insert ⟨type, levels.toList⟩ }

partial def exposeInstance (e : Expr) : MetaM Expr := do
  let (name, args) := getAppFnArgs e
  let env ← getEnv
  if let some info := env.find? name then
    if !isGlobalInstance env name then
      if let some value := info.value? then
        return ← exposeInstance (← whnfR (mkAppN value args))
  return e

partial def skeleton (e : Expr) : MonoM (Option Expr) := do
  withApp e fun fn args => do
    if let some (_, type, levels) ← asHead fn then
      let mvarlevels ← mkFreshLevelMVars levels.length
      let fn := fn.instantiateLevelParams levels mvarlevels
      let (metas, binders, _) ← forallMetaTelescopeReducing
        (type.instantiateLevelParams levels mvarlevels)
      if metas.size != args.size then return none -- eta check.
      for i in [0:binders.size] do
        if binders[i]!.isInstImplicit then
          if let some skeleton ← skeleton (← exposeInstance args[i]!) then
            let _ ← registerInstance skeleton
            let success ← isDefEq metas[i]! skeleton
            if !success then
              logWarning s!"Monomorphization failure: {e}"
              return none
          else return none
      return ← instantiateMVars (mkAppN fn metas)
    else return none

partial def preprocessMono (e : Expr) : MonoM Expr := do
  withApp e fun fn _ => do
    if let some (fn, type, _) ← asHead fn then
      let hasInstImplicit ← forallTelescopeReducing type fun xs _ =>
        do xs.anyM fun x => do pure (← x.fvarId!.getBinderInfo).isInstImplicit
      if hasInstImplicit then
        let set := (← get).mono.getD fn []
        for ⟨id, levels, value⟩ in set do
          let mvarlevels ← mkFreshLevelMVars levels.length
          let instantiated := value.instantiateLevelParams levels mvarlevels
          let ⟨metas, _, body⟩ ← lambdaMetaTelescope instantiated
          if ← isDefEqGuarded e body then
            return mkAppN (.mvar id) (← metas.mapM instantiateMVars)

        if let some skeleton ← skeleton e then
          if ← onlyGlobalFVars skeleton then
            let skeleton ← instantiateMVars skeleton
            let ⟨paramNames, mvars, abstracted⟩ ← abstractMVars skeleton
            let name := Name.mkSimple (((← toName fn).num set.length).toStringWithSep "_" true)
            let mvar := (← mkFreshExprMVar (← inferType
              (abstracted.instantiateLevelParams paramNames.toList (← mkFreshLevelMVars paramNames.size))) .syntheticOpaque name).mvarId!
            modify fun s => { s with
              mono := s.mono.insert fn (⟨mvar, paramNames.toList, abstracted⟩ :: set)
            }
            let _ ← addConstants skeleton.getUsedConstantsAsSet
            let success ← isDefEq skeleton e
            if !success then
              logWarning s!"Failed to monomorphize {fn}"
              return e
            return ← instantiateMVars (mkAppN (.mvar mvar) mvars)
    return e

def exit : MonoM Unit := do
  (← get).mono.values.flatten.forM fun mono =>
    do if !(← mono.id.isAssigned) then
        mono.id.assign mono.assignment

partial def transform [Monad n] [MonadControlT MetaM n] (e : Expr) (f : Expr → n Expr) : n Expr := do
  match ← f e with
  | app fn arg =>
    return .app (← transform fn f) (← transform arg f)
  | lam name type body info =>
    withLocalDecl name info type fun fvar => do
      return .lam name (← transform type f)
        ((← transform (body.instantiate1 fvar) f).abstract #[fvar]) info
  | forallE name type body info =>
    withLocalDecl name info type fun fvar => do
      return .forallE name (← transform type f)
        ((← transform (body.instantiate1 fvar) f).abstract #[fvar]) info
  | letE name type value body nonDep =>
    withLetDecl name type value fun fvar => do
      return .letE name (← transform type f) (← transform value f)
        ((← transform (body.instantiate1 fvar) f).abstract #[fvar]) nonDep
  | mdata m b => return .mdata m (← transform b f)
  | _ => return e

partial def getInstanceTypes (e : Expr) : MetaM (HashSet Expr) := do
  match e with
  | app _ _ =>
      let (fn, args) := Expr.getAppFnArgs e
      if let some info := (← getEnv).find? fn then
        let bs ← getBinders info.type
        let insts ← (bs.toArray.zip args).filterMapM fun ⟨binfo, arg⟩ => do
          if !binfo.isInstImplicit || arg.hasLooseBVars then
            return none
          else some <$> inferType arg
        args.foldlM (fun acc a => return acc ∪ (← getInstanceTypes a)) (HashSet.ofArray insts)
      else
        return ∅
  | mdata _ b | lam _ _ b _ | letE _ _ _ b _ => getInstanceTypes b
  | _ => return ∅

partial def unify (todo : List Expr) (given : List Abstracted) (cb : MonoM (Option Expr)) : MonoM (List Expr) := do
  match todo with
  | [] => return (← cb).toList
  | type :: todo =>
    let type ← instantiateMVars type
    if type.hasMVar then
      let branches ← given.filterMapM fun (inst : Abstracted) => do
        withoutModifyingMCtx do
          let (_, _, inst) ← lambdaMetaTelescope
            (inst.expr.instantiateLevelParams inst.levels (← mkFreshLevelMVars inst.levels.length))
          if ← isDefEqGuarded type inst then
            return some (← unify todo given cb)
          else return none
      if !branches.isEmpty then
        return branches.flatten
    unify todo given cb

def monomorphizeImpl (name : Name) : MonoM (List Expr) := do
  let constInfo ← getConstInfo name

  let levels ← constInfo.levelParams.mapM fun _ => mkFreshLevelMVar

  let typeInstantiated := constInfo.type.instantiateLevelParams constInfo.levelParams levels
  let (mvars, binders, body) ← forallMetaTelescopeReducing typeInstantiated

  let instImplicit := (mvars.zip binders).filterMap fun ⟨m, binfo⟩ =>
    if binfo.isInstImplicit then some m else none

  let instImplicitTypes ← instImplicit.mapM fun mvar => do mvar.mvarId!.getType
  let todo := (← getInstanceTypes body).insertMany instImplicitTypes.toList -- what are the universe levels of todo?

  unify todo.toList (← get).given.toList do
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

    -- check if it's already in the MonoM.
    let result := updateLambdaBinderInfos abstrResult.expr binfos.toList

    let set := (← get).mono.getD (Expr.const name (levels.map fun _ => Level.zero)) []
    for mono in set do
      let sameLevels := mono.assignment.instantiateLevelParams mono.levels (abstrResult.paramNames.toList.map Level.param)
      if sameLevels == result then
        return none

    -- The proper thing to do is to return the levels, too
    let result := result.instantiateLevelParams abstrResult.paramNames.toList (abstrResult.paramNames.toList.map (fun _ => Level.zero))

    let _ ← addConstants result.getUsedConstantsAsSet

    return result

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

structure MonoConfig where
  canonicalize : Bool := true

declare_config_elab monoConfig MonoConfig

def monomorphizeTactic (goal : MVarId) (ids : Array Syntax) (config : MonoConfig) : MonoM MVarId := do
  let _ ← transformMVar goal fun e => transform e preprocessMono -- all instances are in the MonoM

  if !config.canonicalize then
    modify fun s => { s with mono := .emptyWithCapacity 0 }

  let consts ← ids.mapM resolveGlobalConstNoOverload
  -- we don't foldlM immediately because we need the index.
  let exprs : List (Name × Expr) ← consts.toList.flatMapM fun const => do
    let results ← monomorphizeImpl const
    return results.mapIdx fun idx expr =>
      let name := Name.mkSimple ((const.num idx).toStringWithSep "_" true)
      (name, expr)

  let goal ← exprs.foldlM (fun goal (name, result) => do
    pure (← MVarId.note goal name result).2
  ) goal

  if config.canonicalize then
    let goal ← (← get).mono.toList.foldlM (fun goal pair => do
      let (_, monos) := pair
      monos.foldlM (fun goal mono => do
        let name := ((← getMCtx).getDecl mono.id).userName
        let noteResult ← MVarId.note goal name mono.assignment
        mono.id.assign (.fvar noteResult.1)
        pure noteResult.2
      ) goal
    ) goal

    let (type, lctx) ← transformMVar goal fun e => transform e preprocessMono
    let _ ← exit
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
