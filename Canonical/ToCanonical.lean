import Canonical.Basic
import Canonical.Util
import Canonical.Monomorphize
import Canonical.Reduction
import Canonical.Simp
import Canonical.TranslationUtil
import Lean

open Lean hiding Term
open Meta Expr Std Monomorphize

namespace Canonical

mutual

  partial def toTyp (e : Expr) : ToCanonicalM Typ := do
    forallTelescopeReducing e (whnfType := true) fun xs body => do
      let params ← xs.mapM (toVar ·)
      let ids := xs.map (·.fvarId!)
      let arities ← ids.mapM (fun id => do pure (id, ← typeArity (← id.getType)))
      withReader (fun ctx => { ctx with arities := ctx.arities.insertMany arities } ) do
        let paramTypes ← withReader (fun ctx => { ctx with polarity := flip ctx.polarity }) do
          ids.mapM toBind

        return { paramTypes, params, spine := ← toSpine body }

  partial def toBind (id : FVarId) : ToCanonicalM (Option Typ) := do
    if (← id.getBinderInfo).isInstImplicit && (← read).config.monomorphize then
      match (← read).polarity with
      | .premise => return none
      | .goal => return some (← defineInstance)
    return some (← toTyp (← id.getType))

  partial def toTerm (e : Expr) (type : Expr) (arities : List Arity) (params : Array Var := #[]) : ToCanonicalM Term := do
    match ← whnf type with
    | forallE name binderType body info =>
      withLocalDecl name info binderType fun fvar =>
        match arities with
        | [] =>
          withReader (fun ctx => { ctx with arities := ctx.arities.insert fvar.fvarId! {} }) do
            let e := mkApp3 (const ``Pi.mk [← getLevel binderType, ← getLevel (body.instantiate1 fvar)])
              binderType (lam name binderType body info) e
            toTerm e (← inferType e) [] params
        | arity :: arities =>
          withReader (fun ctx => { ctx with arities := ctx.arities.insert fvar.fvarId! arity }) do
            toTerm (app e fvar) (body.instantiate1 fvar) arities (params.push (← toVar fvar))
    | _ =>
      assert! arities.isEmpty
      return { params, spine := ← toSpine (← whnf e) }

  partial def toSpine (e : Expr) : ToCanonicalM Spine := do
    let e ← elimSpecial e
    let e ← if (← read).config.monomorphize then preprocessMono e else pure e
    withApp e fun fn args => do
      let (head, type) ← toHead fn
      let arity ← match fn with
      | fvar id => do
        if !(← read).arities.contains id then
          dbg_trace head
        pure ((← read).arities[id]!)
      | const name _ => defineConst name
      | _ => define head.toString type
      return ← addArgs { head := head.toString } type args.toList arity.params.toList

  partial def addArgs (spine : Spine) (type : Expr) (args : List Expr) (arities : List Arity) : ToCanonicalM Spine := do
    match ← whnf type with
    | forallE name binderType body info =>
      if (← read).config.monomorphize && info.isInstImplicit then
        let _ ← defineInstance
        return ← addArgs { spine with args := spine.args.push { spine := { head := "<synthInstance>" } } } (body.instantiate1 args.head!) args.tail! arities.tail

      let spine ← match arities with
      | [] => do
        pure { head := (``Pi.f).toString, args := #[
          ← toTerm binderType (.sort .zero) {}, -- argument type
          ← toTerm (.lam name binderType body info)
                       (.forallE name binderType (.sort .zero) info) [{}], -- output type
          { spine }, -- function
          ← toTerm args.head! binderType {} -- argument
        ]}
      | arity :: _ => do
        let arg ← toTerm args.head! binderType arity.params.toList
        pure { spine with args := spine.args.push arg }
      addArgs spine (body.instantiate1 args.head!) args.tail! arities.tail
    | _ =>
      assert! args.isEmpty
      return spine

  partial def define (name : String) (type : Expr)
    (onDefine : ToCanonicalM Unit := do pure ()) (onType : ToCanonicalM Unit := do pure ()) : ToCanonicalM Arity := do
    withReader (fun ctx => { ctx with polarity := .premise }) do
      if !(← get).definitions.contains name then
        let defn := { type := .undef, arity := ← typeArity type }
        modify fun state => { state with definitions := state.definitions.insert name defn }
        let _ ← onDefine

      if (← get).numTypes == MAX_TYPES then
        modify (fun state => { state with numTypes := MAX_TYPES + 1 })
        logWarning s!"Runaway definitions! No longer defining types."
      let defineType := !(← read).noTypes && (← get).numTypes < MAX_TYPES

      let defn := (← get).definitions[name]!
      if defn.type matches .undef && defineType then
        let _ ← setType name .none
        modify (fun state => { state with numTypes := state.numTypes + 1 })
        let type ← toTyp type
        let _ ← setType name (.some type)
        let _ ← onType
      return defn.arity

  partial def onDefineConst (name : Name) : ToCanonicalM Unit := do
    let _ ← addConstant name
    let rules ← constRules name
    let success ← addConstraints rules
    if !success then
      logWarning s!"Rules {rules} for {name} are non-terminating."
    else modify fun state => { state with definitions := state.definitions.modify name.toString (fun defn =>
      { defn with rules := defn.rules ++ rules }) }
    pure ()

  partial def constRules (name : Name) : ToCanonicalM (Array Rule) := do
    let decl ← getConstInfo name
    if ← Lean.isIrreducible name then
      return #[]
    if let some info := (← getEnv).getProjectionFnInfo? name then
      let ctorInfo ← getConstInfoCtor info.ctorName
      let _ ← defineConst info.ctorName
      return #[projRule name.toString info (info.ctorName.toString) ctorInfo (← typeArity1 decl.type)]
    if ← isMatcher name then
      let eqns ← Match.getEquationsFor name
      return ← eqns.eqnNames.mapM fun eqn => do
        pure (← toRule #[eqn.toString] (← getConstInfo eqn).type).get!
    if let some eqns ← getEqnsFor? name then
      return ← eqns.mapM fun eqn => do
        pure (← toRule #[eqn.toString] (← getConstInfo eqn).type).get!
    match decl with
    | .recInfo info =>
      return ← info.rules.toArray.mapM fun r => do
        let type ← inferType r.rhs
        let term ← toTerm r.rhs type (← typeArity type).params.toList
        pure (recRule name info r.ctor (← getConstInfoCtor r.ctor) term)
    | .defnInfo info =>
      let includeType := !isAuxRecursor (← getEnv) name || (← isRecursive info.value)
      if !includeType then
        let _ ← setType name.toString .none
      withReader (fun ctx => { ctx with noTypes := includeType }) do
        let defn ← toTerm info.value decl.type (← typeArity decl.type).params.toList
        return #[defRule name.toString defn]
    | _ => return #[]

  partial def onTypeConst (name : Name) : ToCanonicalM Unit := do
    if let .inductInfo info ← getConstInfo name then
      let env ← getEnv
      for ctor in info.ctors do
        let _ ← defineConst ctor

      withReader (fun ctx => { ctx with noTypes := true}) do
        let _ ← defineConst ``False
        let _ ← defineConst ``Eq

      let rules ← reduceCtorEqRules name info
      let success ← addConstraints rules
      assert! success
      modify (fun x =>
        let new := x.definitions.modify (`Eq).toString fun eq =>
          { eq with rules := eq.rules ++ rules }
        { x with definitions := new }
      )

      if let some info := getStructureInfo? env name then
        for field in info.fieldInfo do
          let _ ← defineConst field.projFn
      else
        let _ ← defineConst (mkRecName name)

  partial def defineConst (name : Name) : ToCanonicalM Arity := do
    define name.toString (← getConstInfo name).type (onDefineConst name) (onTypeConst name)

  partial def toRule (attribution : Array String) (e : Expr) (returnInvalid : Bool := true) : ToCanonicalM (Option Rule) :=
    forallTelescopeReducing e fun xs e =>
      (eq? e).bindM fun ⟨typ, lhs, rhs⟩ => do
        forallTelescopeReducing typ fun txs _ => do
          let arities ← (xs ++ txs).mapM (fun x => do
            let id := x.fvarId!
            pure (id, ← typeArity (← id.getType)))
          withReader (fun ctx => { ctx with arities := ctx.arities.insertMany arities }) do
            -- convert an equality of functions into an extensional equality of their applications
            let lhs ← toSpine (← whnf (mkAppN lhs txs))
            if returnInvalid || (← validSimpLemma (xs ++ txs) lhs) then
              return some ⟨lhs, ← toSpine (← whnf (mkAppN rhs txs)), attribution, true⟩
            else return none

end

def definePremise (name : Name) : ToCanonicalM Unit := do
  let info ← getConstInfo name
  if (← read).config.monomorphize then
    if (← getBinders info.type).contains .instImplicit then
      for ⟨expr, idx⟩ in (← monomorphizeImpl name).zipIdx do
        let monoName := Name.mkSimple ((name.num idx).toStringWithSep "_" true)
        let mvar := (← mkFreshExprMVar (← inferType expr) .syntheticOpaque monoName).mvarId!
        mvar.assign expr
        let (mvarName, mvarType) ← toHead (.mvar mvar)
        let _ ← define mvarName.toString mvarType
        -- TODO what if these can be registered as reduction rules?
        return

  if (← read).config.simp then
    if let some rule ← toRule #[name.toString] info.type false then
      if ← addConstraints #[rule] then
        modify fun s => { s with
          definitions := s.definitions.modify rule.lhs.head fun defn => { defn with
            rules := defn.rules.push rule
          }
        }
        return

  let _ ← defineConst name

def toCanonical_ (goal : Expr) (premises : Array Name) : ToCanonicalM Typ := do
  let lets : Array (Let × Option Typ) := ← withReader (fun ctx => { ctx with polarity := .premise }) do
    (← getLCtx).foldlM (fun lets decl => do
      if !decl.isAuxDecl then
        let (name, type) ← toHead decl.toExpr
        if let some value := decl.value? then
          let rule := defRule name.toString (← toTerm value type (← typeArity type).params.toList)
          pure (lets.push ⟨{ name := name.toString, rules := #[rule] }, none⟩)
        else
          pure (lets.push ⟨{ name := name.toString }, ← toBind decl.fvarId⟩)
      else pure lets
    ) #[]

  let typ ← toTyp goal

  withReader (fun ctx => { ctx with polarity := .premise }) do
    for premise in premises do
      let _ ← definePremise premise

  if (← read).config.simp then
    withReader (fun ctx => { ctx with polarity := .premise }) do
      let mut attempted ← getConstants
      while ← consumeDirty do
        let thms ← getRelevantSimpTheorems (← getConstants)
        for thm in thms do
          if !attempted.contains thm then
            attempted := attempted.insert thm
            if let some rule ← toRule #[thm.toString] (← getConstInfo thm).type false then
              if ← addConstraints #[rule] then
                modify fun s => { s with
                  definitions := s.definitions.modify rule.lhs.head fun defn => { defn with
                    rules := defn.rules.push rule
                  }
                }

  let lets : Array (Let × Option Typ) :=
    lets ++ (← get).definitions.toArray.map fun ⟨name, defn⟩ => ({ name, rules := defn.rules }, defn.type.toOption)

  let _ ← exit

  return { typ with
    letTypes := lets.map Prod.snd ++ typ.letTypes,
    lets := lets.map Prod.fst ++ typ.lets
  }

def toCanonical (goal : Expr) (premises : Array Name) (config : CanonicalConfig) : MetaM Typ := do
  let lctx ← getLCtx
  (((toCanonical_ goal premises).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size), config
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds, constants := .ofList [``OfNat.ofNat] }
