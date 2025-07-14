import Canonical.Basic
import Canonical.Util
import Canonical.Monomorphize
import Canonical.Reduction
import Lean

open Lean hiding Term
open Meta Expr Std Monomorphize

namespace Canonical


structure Definition where
  type: LOption Typ
  arity: Arity
  rules: Array Rule := #[]
  neighbors: HashSet String := {}
deriving Inhabited

structure Context where
  arities: HashMap FVarId Arity
  noTypes: Bool := false

structure State where
  definitions: HashMap String Definition := {}
  numTypes: Nat := 0

abbrev ToCanonicalM := ReaderT Context $ StateRefT State MonoM

def toVar (e : Expr) : MetaM Var := do pure { name := ← toNameString e }

def setType (key : String) (typ : LOption Typ) : ToCanonicalM Unit := do
  modify fun state => { state with definitions := state.definitions.modify key (fun x => { x with type := typ }) }

def MAX_TYPES := 100

/-- Some Lean Π-types cannot be converted into Canonical Π-types,
    and are instead converted into this structure. -/
structure Pi (A : Type u) (B : A → Type v) where
  f : (a : A) → B a

/-- Monad for maintaining visited in DFS. -/
abbrev WithVisited := StateT (HashSet String) Id

private partial def cyclicHelper (g : HashMap String Definition) (u : String)
    (stack : HashSet String) : WithVisited Bool := do
  if stack.contains u then
    pure true
  else if (← get).contains u then
    pure false
  else
    modify (·.insert u)
    g[u]!.neighbors.toList.anyM (λ v => cyclicHelper g v (stack.insert u))

/-- Determines whether the `neigbors` adjacency arrays in `g` are cyclic. -/
def cyclic (g : HashMap String Definition) : Bool :=
  (g.toList.anyM (λ (⟨u, _⟩ : String × Definition) => cyclicHelper g u {})).run' {}

/-- Adds an edge to `g` corresponding to the lexicographic path ordering. -/
partial def withConstraint (lhs rhs : Spine) (g : HashMap String Definition) : Option (HashMap String Definition) :=
  (g.get? lhs.head).bind (fun defn =>
    if !g.contains rhs.head then
      g
    else if lhs.head == rhs.head then
      (lhs.args.zip rhs.args).firstM (fun ⟨l, r⟩ => withConstraint l.spine r.spine g)
    else
      g.insert lhs.head { defn with neighbors := defn.neighbors.insert rhs.head }
  )

/-- Adds termination constraints for `rules` in the form of edges in `g`. -/
def addConstraints (rules : Array Rule) : ToCanonicalM Bool := do
  let g := (← get).definitions
  if let some g := rules.foldlM (fun g rule => withConstraint rule.lhs rule.rhs g) g then
    if !cyclic g then do
      modify fun state => { state with definitions := g }
      return true
  return false

def elimSpecial (e : Expr) : MetaM Expr := do
  withApp e fun fn args =>
    match fn with
    | forallE name type body info => do
      assert! args.isEmpty
      let l2 ← withLocalDecl name info type fun fvar => getLevel (body.instantiate1 fvar)
      return (mkApp2 (.const ``Pi [← getLevel type, l2]) type (.lam name type body info))
    | lit l => do
      assert! args.isEmpty
      if let .natVal n := l then
        if n <= 5 then
          return rawRawNatLit n
      return e
    | proj type idx struct => do
      let info := getStructureInfo (← getEnv) type
      return mkAppN (← mkProjection struct info.fieldNames[idx]!) args
    | _ => return e

mutual

  partial def toTyp (e : Expr) : ToCanonicalM Typ := do
    forallTelescopeReducing e (whnfType := true) fun xs body => do
      let params ← xs.mapM (toVar ·)
      let ids := xs.map (·.fvarId!)
      let types ← ids.mapM (·.getType)
      let arities ← (ids.zip types).mapM (fun ⟨id, type⟩ => do pure (id, ← typeArity type))
      withReader (fun ctx => { ctx with arities := ctx.arities.insertMany arities } ) do
        let paramTypes ← types.mapM (fun type => do pure (some (← toTyp type)))
        return { paramTypes, params, spine := ← toSpine body }

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
    withApp (← preprocessMono (← elimSpecial e)) fun fn args => do
      let (head, type) ← toHead fn
      let arity ← match fn with
      | fvar id => do
        if !(← read).arities.contains id then
          dbg_trace head
        pure ((← read).arities[id]!)
      | const name _ => define head.toString type (defineConst name)
      | _ => define head.toString type
      return ← addArgs { head := head.toString } type args.toList arity.params.toList

  partial def addArgs (spine : Spine) (type : Expr) (args : List Expr) (arities : List Arity) : ToCanonicalM Spine := do
    match ← whnf type with
    | forallE name binderType body info =>
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

  partial def define (name : String) (type : Expr) (onDefine : ToCanonicalM Unit := do pure ()) : ToCanonicalM Arity := do
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
    return defn.arity

  partial def defineConst (name : Name) : ToCanonicalM Unit := do
    let _ ← addConstant name
    let rules ← constRules name
    let success ← addConstraints rules
    assert! success
    modify fun state => { state with definitions := state.definitions.modify name.toString (fun defn =>
      { defn with rules := defn.rules ++ rules }) }
    pure ()

  partial def constRules (name : Name) : ToCanonicalM (Array Rule) := do
    let decl ← getConstInfo name
    if ← Lean.isIrreducible name then
      return #[]
    if let some info := (← getEnv).getProjectionFnInfo? name then
      let ctorInfo ← getConstInfoCtor info.ctorName
      let _ ← define info.ctorName.toString ctorInfo.type (defineConst info.ctorName)
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
    | .inductInfo info =>
      let env ← getEnv
      for ctor in info.ctors do
        let _ ← define ctor.toString (env.find? ctor).get!.type (defineConst ctor)

      withReader (fun ctx => { ctx with noTypes := true}) do
        let _ ← define (`False).toString (env.find? `False).get!.type (defineConst `False)
        let _ ← define (`Eq).toString (env.find? `Eq).get!.type (defineConst `Eq)

      let rules ← reduceCtorEqRules decl.name info
      let success ← addConstraints rules
      assert! success
      modify (fun x =>
        let new := x.definitions.modify (`Eq).toString fun eq =>
          { eq with rules := eq.rules ++ rules }
        { x with definitions := new }
      )

      if let some info := getStructureInfo? env name then
        for field in info.fieldInfo do
          let _ ← define field.projFn.toString (env.find? field.projFn).get!.type (defineConst field.projFn)
      else
        let _ ← define (mkRecName name).toString (env.find? (mkRecName name)).get!.type (defineConst (mkRecName name))
      return #[]
    | .defnInfo info =>
      let includeType := !isAuxRecursor (← getEnv) name || (← isRecursive info.value)
      if !includeType then
        let _ ← setType name.toString .none
      withReader (fun ctx => { ctx with noTypes := includeType }) do
        let defn ← toTerm info.value decl.type (← typeArity decl.type).params.toList
        return #[defRule name.toString defn]
    | _ => return #[]

  partial def toRule (attribution : Array String) (e : Expr) (returnInvalid : Bool := true) : ToCanonicalM (Option Rule) :=
    forallTelescopeReducing e fun xs e =>
      (eq? e).bindM fun ⟨typ, lhs, rhs⟩ => do
        forallTelescopeReducing typ fun txs _ => do
          let arities ← (xs ++ txs).mapM (fun x => do
            let id := x.fvarId!
            pure (id, ← typeArity (← id.getType)))
          withReader (fun ctx => { ctx with arities := ctx.arities.insertMany arities }) do
            -- convert an equality of functions into an extensional equality of their applications
            let lhs ← whnf (mkAppN lhs txs)
            let rhs ← whnf (mkAppN rhs txs)
            let rule := ⟨← toSpine lhs, ← toSpine rhs, attribution, true⟩
            if returnInvalid || (← validSimpLemma (xs ++ txs) rule) then
              return some rule
            else return none

end

def toCanonical_ (goal : Expr) (premises : Array Name) : ToCanonicalM Typ := do
  let lets : Array (Let × Option Typ) := ← (← getLCtx).foldlM (fun lets decl => do
    if !decl.isAuxDecl then
      let (name, type) ← toHead decl.toExpr
      if let some value := decl.value? then
        let rule := defRule name.toString (← toTerm value type (← typeArity type).params.toList)
        pure (lets.push ⟨{ name := name.toString, rules := #[rule] }, none⟩)
      else
        let type ← toTyp type
        pure (lets.push ⟨{ name := name.toString }, some type⟩)
    else pure lets
  ) #[]

  for const in premises do
    -- TODO simp, monomorphize
    let _ ← define const.toString (← getConstInfo const).type (defineConst const)

  let typ ← toTyp goal

  -- TODO simp

  let lets : Array (Let × Option Typ) :=
    lets ++ (← get).definitions.toArray.map fun ⟨name, defn⟩ => ({ name, rules := defn.rules }, defn.type.toOption)

  return { typ with
    letTypes := lets.map Prod.snd ++ typ.letTypes,
    lets := lets.map Prod.fst ++ typ.lets
  }

def toCanonical (goal : Expr) (premises : Array Name) : MetaM Typ := do
  let lctx ← getLCtx
  (((toCanonical_ goal premises).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size)
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds }
    -- TODO ofNat special case?
