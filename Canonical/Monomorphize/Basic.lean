module

import Lean.Meta
import Lean.Elab.ConfigEval
public import Lean.Elab.Tactic.Basic
open Lean Expr Std Meta

namespace Monomorphize

public section

/-- A metavariable and its future intended assignment, to serve as a new symbol during pre-processing. -/
structure MetaAbstraction where
  id: MVarId
  assignment: Expr

inductive Affix where
  /-- Instance arguments, and what they determine. -/
  | insts
  /-- Also type arguments, recursively: `Set α` fixes `α`, `Fin n` keeps `n` as an argument.
      Operations without instance arguments get symbols too, and premise copies are also unified
      with the types in the goal. -/
  | types
  | typeParameters
  deriving Ord

instance : LE Affix := leOfOrd

/-- State monad for monomorphization -/
structure MonoState where
  /-- A mapping from symbols (consts, fvars, mvars) to their monomorphizations. -/
  mono: HashMap Expr (List MetaAbstraction) := .emptyWithCapacity 8
  /-- Types of instances relevant to the problem. For `affix ≥ types`, also the closed types in the
      goal and hypotheses, including the types of their closed subterms. -/
  candidateInsts: HashSet Expr := .emptyWithCapacity 8
  /-- Type arguments relevant to the problem, for `affix ≥ types`. -/
  candidateTypes: HashSet Expr := .emptyWithCapacity 8
  /-- How much of an occurrence a symbol fixes. -/
  affix: Affix := .insts
  /-- FVars that are safe to be used in the definition of monomorphizations. -/
  globalFVars: HashSet FVarId := .emptyWithCapacity 0
  /-- Names of all constants we encounter. -/
  constNames: NameSet := .empty
  /-- "Dirty" flag for `constNames`. -/
  hasNewConst: Bool := true

instance : ToString MonoState where
  toString s := s!"{s.mono.toList.map fun x => x.1}\n{s.candidateInsts.toList}"

abbrev MonoM := StateRefT MonoState MetaM

/-- Needed for `withoutModifyingState`. The `MonoState` is not part of the saved state. -/
instance : MonadBacktrack Meta.SavedState MonoM := ⟨Meta.saveState, fun s => s.restore⟩

/-- Add `name` to `constNames`. -/
def addConstant (name : Name) : MonoM Unit := do
  modify fun s => { s with
    constNames := s.constNames.insert name,
    hasNewConst:= s.hasNewConst || !s.constNames.contains name
  }

/-- Add `names` to `constNames`. -/
def addConstants (names : NameSet) : MonoM Unit := do
  modify fun s => { s with
    constNames := s.constNames.insertMany names,
    hasNewConst := s.hasNewConst || !names.all s.constNames.contains
  }

def getConstants : MonoM NameSet := do
  return (← get).constNames

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

/-- The type of the instance `inst` and the types of its parent-class instance. -/
partial def instanceTypes (inst : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  let type ← inferType inst
  if acc.contains type then return acc
  let acc := acc.push type
  let .const c us := type.getAppFn | return acc
  let env ← getEnv
  unless isStructure env c do return acc
  (getStructureParentInfo env c).foldlM (init := acc) fun acc p => do
    unless isClass env p.structName do return acc
    instanceTypes (mkAppN (.const p.projFn us) (type.getAppArgs.push inst)) acc

/-- Add a typeclass instance to `candidateInsts`, or a type to `candidateTypes`. -/
partial def addAsCandidate (e : Expr) (isType := false) : MonoM Unit := do
  if ← onlyHasGlobalFVars e then
    let types ← if isType then pure #[e] else instanceTypes e
    for type in types do
      let ⟨_, _, type⟩ ← abstractMVars type (levels := false)
      modify fun s => if isType then { s with candidateTypes := s.candidateTypes.insert type }
        else { s with candidateInsts := s.candidateInsts.insert type }

/-- If `id` is instImplicit, add its type to `candidateInsts`. -/
def addFVarAsCandidate (id : FVarId) : MonoM Unit := do
  assert! (← id.getBinderInfo).isInstImplicit
  addAsCandidate (.fvar id)

/-- Unfolds constants that are not global instances at the head of `e`.  -/
partial def unfoldInstDefn (e : Expr) : MetaM Expr := do
  if let .const name us := e.getAppFn then
    let env ← getEnv
    if let some info := env.find? name then
      if !(← isInstance name) && !(← isProjectionFn name) then
        if let some value := info.value? then
          return ← unfoldInstDefn (← whnfR
            (mkAppN (value.instantiateLevelParams info.levelParams us) e.getAppArgs))
  return e

/-- Apply `transform` to the type and local context of `goal`. -/
def transformMVar [Monad n] [MonadLiftT MetaM n] [MonadMCtx n] (goal : MVarId) (transform : Expr → n Expr) : n (Expr × LocalContext) := do
  let decl := ((← getMCtx).findDecl? goal).get!
  let type ← transform (← instantiateMVars decl.type)

  let mut lctx := decl.lctx
  for ldecl in decl.lctx do
    if ldecl.isImplementationDetail then continue
    let mut newDecl := ldecl.setType (← transform (← instantiateMVars ldecl.type))
    if let some value := ldecl.value? then
      newDecl := newDecl.setValue (← transform value)
    lctx := lctx.modifyLocalDecl ldecl.fvarId fun _ => newDecl

  return (type, lctx)

/-- Abstract all non-affixed subterms in `e` into metavaraibles. -/
partial def monoPattern (e : Expr) : MonoM (Option Expr) := do
  withApp e fun fn args => do
    let some (_, type, levels) ← getHeadInfo fn | return none
    let us := if let .const _ us := fn then us else []
    let (metas, binders, _) ← forallMetaTelescopeReducing
      (type.instantiateLevelParams levels us) args.size
    -- Check that `e` is eta expanded.
    if metas.size != args.size then return none
    let affix := (← get).affix
    for i in [0:binders.size] do
      let type ← metas[i]!.mvarId!.getType
      let whole := affix matches .typeParameters && type.isType
      let pattern := binders[i]!.isInstImplicit && (← isClass? type).isSome || affix ≥ .types && type.isSort
      unless whole || pattern do continue
      -- The argument still has a metavariable in it: nothing to specialize yet.
      if args[i]!.hasExprMVar then return none
      let some fixed ← if whole then pure (some args[i]!) else monoPattern (← unfoldInstDefn args[i]!)
        | return none
      addAsCandidate fixed (isType := type.isSort)
      -- Assign `metas[i]` to `fixed`. Use `isDefEq` to create a valid term.
      unless ← isDefEqGuarded metas[i]! fixed do
        logWarning s!"Monomorphization failure: {e}"
        return none
    instantiateMVars (mkAppN fn metas)

/-- `isDefEq` that also assigns metavariables within proof arguments of `pattern`,
    which `isDefEq` skips by proof irrelevance. -/
partial def isDefEqProofRelevant (pattern e : Expr) : MetaM Bool := withoutProofIrrelevance do
  let fn := pattern.getAppFn
  if fn.isConst && fn.constName? == e.getAppFn.constName? && pattern.getAppNumArgs == e.getAppNumArgs then
    isDefEqGuarded fn e.getAppFn <&&> (pattern.getAppArgs.zip e.getAppArgs).allM fun (p, a) => isDefEqProofRelevant p a
  else isDefEqGuarded pattern e

def eligibleHead (e type : Expr) (affix : Affix) : MetaM Bool := do
  unless e.isApp do return false
  forallTelescopeReducing type fun xs body => do
    if ← xs.anyM fun x => do pure (← x.fvarId!.getBinderInfo).isInstImplicit then return true
    unless affix ≥ .types && !body.isSort do return false
    xs.anyM fun x => do pure (← x.fvarId!.getType).isSort

/-- Monomorphizes the head of `e`, creating a new monomorphization metavariable if necessary. -/
partial def monoTransformStep (e : Expr) : MonoM TransformStep := do
  withOptions (backward.isDefEq.respectTransparency.set · false) do withApp e fun fn _ => do
    if let some (fn, type, _) ← getHeadInfo fn then
      if ← eligibleHead e type (← get).affix then
        -- Check if we can use a pre-existing monomorphization.
        let cachedSpec := (← get).mono.getD fn []
        for ⟨specmVar, specBody⟩ in cachedSpec do
          if let some result ← Meta.withNewMCtxDepth do
              let (metas, _, body) ← lambdaMetaTelescope specBody
              if ← isDefEqProofRelevant body e then
                pure (some (mkAppN (.mvar specmVar) (← metas.mapM instantiateMVars)))
              else pure none then
            return .continue result

        -- Otherwise, create a monomorphization.
        let some (abstracted, args) ← Meta.withNewMCtxDepth do
            let some monoPattern ← withConfig ({ · with univApprox := false }) do monoPattern e | return none
            unless ← onlyHasGlobalFVars monoPattern do return none
            let monoPattern ← instantiateMVars monoPattern
            -- Abstract monoPattern before isDefEq, so as to not assign the mvars.
            let ⟨_, mvars, abstracted⟩ ← abstractMVars monoPattern (levels := false)
            let _ ← addConstants monoPattern.getUsedConstantsAsSet

            let success ← isDefEqProofRelevant monoPattern e
            if !success then
              logWarning s!"Failed to monomorphize {fn}"
              return none
            return some (abstracted, ← mvars.mapM instantiateMVars)
          | return .continue
        let specName := Name.mkSimple (((← toName fn).num cachedSpec.length).toStringWithSep "_" true)
        let specMvar ← mkFreshExprMVar (← inferType abstracted) .syntheticOpaque specName
        -- Add this to mono state.
        modify fun s => { s with mono := s.mono.insert fn (⟨specMvar.mvarId!, abstracted⟩ :: cachedSpec) }
        return .continue (mkAppN specMvar args)
    return .continue

def preprocessMono (e : Expr) : MonoM Expr := do
  match ← monoTransformStep e with
  | .done e | .visit e | .continue (some e) | _ => return e

/-- Perform the assignments given by the `MetaAbstractions` in `mono`. -/
def finalizeMonos : MonoM Unit := do
  (← get).mono.values.flatten.forM fun mono =>
    do if !(← mono.id.isAssigned) then
      mono.id.assign mono.assignment

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
partial def unifyWithCand (todo : List (Expr × List Expr)) (cb : MonoM (Option Expr)) : MonoM (List Expr) := do
  match todo with
  | [] => return (← cb).toList
  | (type, candidates) :: todo =>
    let type ← instantiateMVars type
    -- If there is unification to be done,
    if type.hasMVar then
      -- For each candidate instance,
      let branches ← candidates.filterMapM fun (inst : Expr) => do
        withoutModifyingState do -- fork the MCtx to consider each branch independently
          -- Abstract over lambda bindings.
          let (_, _, inst) ← lambdaMetaTelescope inst
          if ← isDefEqGuarded type inst then
            -- continue unifying the remainder of `todo`.
            return some (← unifyWithCand todo cb)
          else return none
      if !branches.isEmpty then
        return branches.flatten
    -- If there is no unification, we continue anyway.
    unifyWithCand todo cb

/-- The body of `monomorphizeConst`. -/
def monomorphizeConstCore (name : Name) : MonoM (List Expr) := do
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
  -- For `affix ≥ types`, also unify the type parameters with the candidate types.
  let typeParams ← if (← get).affix ≥ .types then
      mvars.filterM fun m => do pure (← m.mvarId!.getType).isSort
    else pure #[]
  let (insts, types) := ((← get).candidateInsts.toList, (← get).candidateTypes.toList)
  withOptions (backward.isDefEq.respectTransparency.set · false) do
  unifyWithCand (todo.toList.map (·, insts) ++ typeParams.toList.map (·, types)) do
    for mvar in instImplicit do
      let mty ← instantiateMVars (← mvar.mvarId!.getType)
      match ← trySynthInstance mty with
      | .some inst => do let _ ← isDefEqGuarded mvar inst
      | .none => return none
      | .undef => pure ()

    -- Solve the universe constraints postponed during unification. No copy if that fails.
    unless ← processPostponed (mayPostpone := false) do return none
    -- A hypothesis cannot be universe polymorphic, so any level still undetermined is set to zero.
    for l in levels do
      if let .mvar m := l then
        unless ← isLevelMVarAssigned m do
          assignLevelMVar m .zero
    let appliedExpr := mkAppN (Expr.const name levels) mvars
    let instantiated ← instantiateMVars appliedExpr
    let abstrResult ← abstractMVars instantiated (levels := false)
    let binfos := abstrResult.mvars.map fun mvar =>
      (mvars.idxOf? mvar).map fun idx => binders[idx]!

    -- Check if this constant already has this monomorphization.
    let result := updateLambdaBinderInfos abstrResult.expr binfos.toList
    let set := (← get).mono.getD (Expr.const name (levels.map fun _ => Level.zero)) []
    for mono in set do
      if mono.assignment == result then
        return none

    let _ ← addConstants result.getUsedConstantsAsSet

    return result

/-- Generates all monomorphizations for a given constant. -/
def monomorphizeConst (name : Name) : MonoM (List Expr) :=
  (·.eraseDups) <$> Meta.withNewMCtxDepth (monomorphizeConstCore name)

structure MonoConfig where
  canonicalize : Bool := true
  /-- How much of an occurrence a symbol fixes: `insts`, `types` or `firstOrder`. -/
  affix : Affix := .insts

declare_config_elab monoConfig MonoConfig

def monomorphizeTactic (goal : MVarId) (ids : Array Syntax) (config : MonoConfig) : MonoM MVarId := do
  -- Consider instImplicit local decls.
  for decl in ((← getMCtx).findDecl? goal).get!.lctx.decls do
    if let some decl := decl then
      if decl.binderInfo.isInstImplicit then
        addFVarAsCandidate decl.fvarId

  -- First pass: collect `candidateInsts` and ignore the transformation result.
  let _ ← transformMVar goal fun e => do
    Meta.transform e (pre := monoTransformStep)

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
        let noteResult ← MVarId.note goal name mono.assignment
        mono.id.assign (.fvar noteResult.1)
        pure noteResult.2
      ) goal
    ) goal

    -- The second pass substitutes the `monos`.
    let (type, lctx) ← goal.withContext do
      transformMVar goal fun e => Meta.transform e (pre := monoTransformStep)
    -- Failsafe for new `monos` being added during the second pass.
    let _ ← finalizeMonos
    let _ ← goal.modifyLCtx fun _ => lctx
    goal.replaceTargetDefEq type
  else return goal
