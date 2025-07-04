import Lean
-- import Std.Time.DateTime.Timestamp

namespace Canonical

/-- A variable with a `name`, and whether it is proof `irrelevant` (unused). -/
structure Var where
  name: String
  irrelevant: Bool
deriving Inhabited

mutual
  /-- A let declaration, with a name, value and reduction rules. -/
  structure Let where
    name: String
    irrelevant: Bool
    rules: Array Rule
  deriving Inhabited

  /-- A term is an n-ary, β-normal, η-long λ expression:
      `λ params lets . head args` -/
  structure Tm where
    params: Array Var := #[]
    lets: Array Let := #[]
    head: String
    args: Array Tm := #[]

    /- For proof reconstruction, the reduction rules that were
       used to unify the premise with the goal. -/
    premiseRules: Array String := #[]
    goalRules: Array String := #[]
  deriving Inhabited

  /-- A reduction rule `lhs ↦ rhs`. The `attribution` will be added
      to the `premiseRules` or `goalRules` arrays where used.
      Canonical will not return a term that reduces according to
      a rule that `isRedex`. -/
  structure Rule where
    lhs: Tm
    rhs: Tm
    attribution: Array String
    isRedex: Bool
  deriving Inhabited
end

/-- A type is an n-ary Π-type: `Π params lets . codomain` -/
structure Typ where
  params: Array (Option Typ) := #[]
  lets: Array (Option Typ) := #[]
  codomain: Tm
deriving Inhabited

/-- The return type of Canonical, with the generated `terms`. -/
structure CanonicalResult where
  terms: Array Tm
  attempted_resolutions: UInt32
  successful_resolutions: UInt32
  steps: UInt32
  last_level_steps: UInt32
  branching: Float32
deriving Inhabited

@[never_extract, extern "term_to_string"] opaque termToString: @& Tm → String
instance : ToString Tm where toString := termToString

@[never_extract, extern "typ_to_string"] opaque typToString: @& Typ → String
instance : ToString Typ where toString := typToString

/-- Generate terms of a given type, with given timeout and desired count. -/
@[never_extract, extern "canonical"] opaque canonical : @& Typ → UInt64 → USize → IO CanonicalResult

/-- Start a server with the refinement UI on the given type. -/
@[never_extract, extern "refine"] opaque refine : @& Typ → IO Unit

/-- Obtains the current term from the refinement UI. -/
@[never_extract, extern "get_refinement"] opaque getRefinement : IO Tm

/-- Saves a JSON representation of the type to the given file. -/
@[never_extract, extern "save_to_file"] opaque save_to_file : @& Typ → String → IO Unit

instance : ToString Rule where toString := fun r => s!"{r.lhs} ↦ {r.rhs}"

/-- Some Lean Π-types cannot be converted into Canonical Π-types,
    and are instead converted into this structure. -/
structure Pi (A : Type u) (B : A → Type v) where
  f : (a : A) → B a

open Std Lean Elab.Tactic Expr Meta

/-- `define` is a list of names that should be defined
    if this HardCode is triggered -/
structure HardCode where
  define: List Name
  rules: List Name
  simpnf: List Name

/-- Rather than recursively unfolding definitions, `HARD_CODE` overrides
    the definitions introduced by a given symbol. -/
def HARD_CODE : HashMap (Name × Name) HardCode := .ofList [
    ⟨⟨`Mathlib.Data.Real.Basic, `Real⟩, ⟨[], [], []⟩⟩,
    ⟨⟨`Init.Prelude, `Nat.add⟩, ⟨[], [`Nat.add_zero, `Nat.add_succ, `Nat.zero_add, `Nat.succ_add, `Nat.add_assoc], [`Nat.add_eq]⟩⟩,
    ⟨⟨`Init.Prelude, `Nat.mul⟩, ⟨[], [`Nat.mul_zero, `Nat.zero_mul, `Nat.succ_mul, `Nat.mul_succ, `Nat.mul_assoc, `Nat.mul_add, `Nat.add_mul], [`Nat.mul_eq]⟩⟩,
    ⟨⟨`Init.Prelude, `Nat.pow⟩, ⟨[], [`Nat.pow_zero, `Nat.pow_succ, `Nat.pow_add, `Nat.mul_pow], [`Nat.pow_eq]⟩⟩,
    ⟨⟨`Init.Prelude, `Nat.le⟩, ⟨[`Nat.le.refl, `Nat.le.step], [`Nat.le_zero_eq], [`Nat.le_eq]⟩⟩,
    ⟨⟨`Init.Prelude, `Nat.ble⟩, ⟨[], [``Nat.ble.eq_2, ``Nat.ble.eq_3, ``Nat.ble.eq_4], []⟩⟩,
  ]

def getHardCode (name : Name) : CoreM (Option HardCode) := do
  if let some module ← Lean.findModuleOf? name then
    if let some hard_code := HARD_CODE.get? ⟨module, name⟩ then
      pure (some hard_code)
    else pure none
  else pure none

/-- Structure for storing the type and value of let definitions. -/
structure Definition where
  type: Option Typ := none
  irrelevant: Bool := false
  rules: Array Rule := #[]
  shouldReplace: Bool := false
  neighbors: Array Name := #[]
deriving Inhabited

/-- Monad for maintaining visited in DFS. -/
abbrev WithVisited := StateT (HashSet Name) Id

private partial def cyclicHelper (g : AssocList Name Definition) (u : Name)
    (stack : HashSet Name) : WithVisited Bool := do
  if stack.contains u then
    pure true
  else if (← get).contains u then
    pure false
  else
    modify (·.insert u)
    ((g.find? u).getD (panic! "cyclicHelper node not in graph.")).neighbors.anyM (λ v => cyclicHelper g v (stack.insert u))

/-- Determines whether the `neigbors` adjacency arrays in `g` are cyclic. -/
def cyclic (g : AssocList Name Definition) : Bool :=
  (g.toList.anyM (λ (⟨u, _⟩ : Name × Definition) => cyclicHelper g u {})).run' {}

/-- Adds an edge to `g` corresponding to the lexicographic path ordering. -/
partial def addConstraint (lhs : Tm) (rhs : Tm) (g : AssocList Name Definition) : Option (AssocList Name Definition) :=
  (g.find? lhs.head.toName).bind (fun defn =>
    if !g.contains rhs.head.toName then
      g
    else if lhs.head == rhs.head then
      (lhs.args.zip rhs.args).firstM (fun ⟨l, r⟩ => addConstraint l r g)
    else
      g.replace lhs.head.toName { defn with neighbors := defn.neighbors.push rhs.head.toName }
  )

/-- Adds termination constraints for `rules` in the form of edges in `g`. -/
def addConstraints (rules : Array Rule) (g : AssocList Name Definition) : Option (AssocList Name Definition) :=
  rules.foldlM (fun g rule => addConstraint rule.lhs rule.rhs g) g

/-- Counts the occurrences of `v` as a head symbol in `t`. -/
partial def count (t : Tm) (v : String) : Nat :=
  t.args.foldl (init := if t.head == v then 1 else 0) (· + count · v)

/-- Whether this term contains any lambda expressions. -/
partial def containsLambda (t : Tm) : Bool :=
  if t.params.isEmpty then
    t.args.any containsLambda
  else true

/- def print_force (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush -/

/-- When translating to Canonical, we maintain a state of translated constant symbols. -/
abbrev ToCanonicalM := StateT (AssocList Name Definition) MetaM

structure Settings where
  depth: Nat := 0
  simp: Bool

/-- For readability, we identify free variables by their `userName`,
    but with the suffix of the `FVarId.name` for completeness. -/
def name : Expr → MetaM Name
| fvar fvarId => do pure (fvarId.name.updatePrefix (←fvarId.getUserName).getRoot)
| _ => panic! "name of non-fvar"

def nameString (e : Expr) : MetaM String := do pure (←name e).toString

/-- A `Tm` representing a natural number. -/
def natToTerm (n : Nat) : Tm :=
  match n with
  | Nat.zero => { head := (``Nat.zero).toString }
  | Nat.succ n => { head := (``Nat.succ).toString, args := #[natToTerm n] }

/-- The default arity of a type `e`.  -/
partial def forallArity (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | forallE binderName binderType body binderInfo =>
    withLocalDecl binderName binderInfo binderType fun fvar => do
      pure ((← forallArity (instantiate1 body fvar)) + 1)
  | app body _ | lam _ _ body _ | letE _ _ _ body _ | mdata _ body => forallArity body
  | _ => pure 0

/-- The arities of the types of the parameters of type `e`. -/
partial def paramArities (e : Expr) : MetaM (List Nat) := do
  let e ← whnf e
  match e with
  | forallE binderName binderType body binderInfo =>
    withLocalDecl binderName binderInfo binderType fun fvar => do
      pure ((← forallArity binderType) :: (← paramArities (instantiate1 body fvar)))
  | app body _ | lam _ _ body _ | letE _ _ _ body _ | mdata _ body => paramArities body
  | _ => pure []

def isOpaque (info : ConstantInfo) : ToCanonicalM Bool := do
  if ← Lean.isIrreducible info.name then pure false else
  match info with
  | .ctorInfo info => pure (isClass (← getEnv) info.induct)
  | .recInfo _ => pure true
  | .defnInfo _ => pure (isAuxRecursor (← getEnv) info.name)
  | _ => pure false

/- If true, gives a definition with value `expr` a type. -/
def includeLetType (expr : Expr) : ToCanonicalM Bool := do
  match expr with
  | app fn arg => includeLetType fn <||> includeLetType arg
  | lam _ _ body _ | forallE _ _ body _ | letE _ _ _ body _ | mdata _ body => includeLetType body
  | const declName _ =>
    let decl := ((← getEnv).find? declName).getD (panic! "includeLetType: constant not found")
    isOpaque decl
  | _ => pure false

/- If true, gives the surrounding definition a type. -/
def includeType (info : ConstantInfo) : ToCanonicalM Bool := do
  if ← Lean.isIrreducible info.name then pure true else
  match info with
  | .ctorInfo info => pure !(isClass (← getEnv) info.induct)
  | .defnInfo info => pure <| !(isAuxRecursor (← getEnv) info.name) && (← includeLetType info.value)
  | _ => pure true

/-- Rule corresponding to δ-reduction. -/
def defRule (name : String) (defn : Tm) : Rule :=
  ⟨{ head := name, args := defn.params.map (fun p => { head := p.name }) }, { defn with params := #[]}, #[], false⟩

/-- Rule corresponding to ι-reduction -/
def recRule (recursor : Name) (recVal : RecursorVal) (constructor : Name) (constructorVal : ConstructorVal) (rhs : Tm) : Rule :=
  let ctorStart := (recVal.numParams+recVal.numMotives+recVal.numMinors);
  let args : Array Tm := (rhs.params.shrink ctorStart).map (fun p => { head := p.name })
  let ctorArgs : Array Tm := (rhs.params.toSubarray ctorStart (ctorStart + constructorVal.numFields)).toArray.map (fun p => { head := p.name })
  let major : Tm := { head := constructor.toString, args := Array.replicate constructorVal.numParams { head := "*" } ++ ctorArgs}
  let args : Array Tm := (args ++ Array.replicate recVal.numIndices ({ head := "*" } : Tm)).push major
  let args := args ++ (rhs.params.toSubarray (ctorStart + constructorVal.numFields)).toArray.map (fun p => { head := p.name })
  ⟨{head := recursor.toString, args := args }, { rhs with params := #[] }, #[], true⟩

/-- Rule corresponding to reduction of projections. -/
def projRule (projection : String) (projInfo : ProjectionFunctionInfo) (constructor : String) (constructorVal : ConstructorVal) (arity : Nat) : Rule :=
  let ctorArgs : Array Tm := (Array.replicate (constructorVal.numParams + constructorVal.numFields) { head := "*" }).set! (constructorVal.numParams + projInfo.i) { head := "field" }
  let fieldArgs : Array Tm := Array.ofFn (fun (i : Fin (arity - projInfo.numParams - 1)) => { head := "arg" ++ toString i.val })
  let args : Array Tm := ((Array.replicate projInfo.numParams { head := "*"}).push { head := constructor, args := ctorArgs }) ++ fieldArgs
  ⟨{ head := projection, args := args }, { head := "field", args := fieldArgs }, #[], true⟩

/-- Rules for the equality of distinct constructors to reduce to `False`. -/
def reduceCtorEqRules (ind : Name) (info : InductiveVal) : MetaM (Array Rule) := do
  let mut rules := #[]
  for ctor1 in info.ctors do
    for ctor2 in info.ctors do
      if ctor1 != ctor2 then
        let info1 ← getConstInfoCtor ctor1
        let info2 ← getConstInfoCtor ctor2
        rules := rules.push ⟨{ head := "Eq", args := #[
          { head := ind.toString },
          { head := ctor1.toString, args := Array.replicate (info1.numFields + info.numParams + info.numIndices) { head := "*" } },
          { head := ctor2.toString, args := Array.replicate (info2.numFields + info.numParams + info.numIndices) { head := "*" } }
        ] }, { head := "False" }, #["reduceCtorEq"], true⟩
  pure rules

/-- A conservative test for whether a rule (derived from a `simp` lemma) can be added to Canonical. -/
def validSimpLemma (xs : Array Expr) (rule : Rule) : MetaM Bool := do
  if ← xs.anyM (fun x => do pure ((← forallArity (← x.fvarId!.getType)) != 0)) then
    pure false -- higher order
  else if ← xs.anyM (fun x => do pure (count rule.lhs (← nameString x) != 1)) then
    pure false -- unbound or overused variable
  else if containsLambda rule.lhs then
    pure false -- potentially requires fvars do not use the lambda
  else pure true

mutual
  /-- Converts an equation theorem `e` into a rule, if possible. Returns whether the rule is a `validSimpLemma`. -/
  partial def eqnRule (attribution : Array String) (e : Expr) (settings : Settings) : ToCanonicalM (Option (Bool × Rule)) :=
    forallTelescopeReducing e fun xs e =>
      ((eq? e).mapM fun ⟨typ, lhs, rhs⟩ => do
        forallTelescopeReducing typ fun txs typ => do
          let rule := ⟨← toTerm lhs typ settings 0 [] [] txs.toList [], ← toTerm rhs typ settings 0 [] [] txs.toList [], attribution, true⟩
          pure ⟨← validSimpLemma (xs ++ txs) rule, rule⟩
      )

  /-- At present, only small natural numbers are converted into a `Tm`. Other literals are `opaque`. -/
  partial def defineLiteral (val : Literal) (settings : Settings) : ToCanonicalM Tm := do
    match val with
    | .natVal n =>
      if n <= 5 then
        pure (natToTerm n)
      else
        let name := Name.mkSimple (toString n)
        if !(← get).contains name then do
          modify (·.insert name { type := ← toTyp val.type settings, shouldReplace := settings.depth > 0 })
        pure { head := toString n }
    | .strVal s =>
      let name := Name.mkSimple s!"\"{s}\""
      if !(← get).contains name then do
        modify (·.insert name { type := ← toTyp val.type settings, shouldReplace := settings.depth > 0 })
      pure { head := s!"\"{s}\"" }

  /-- Insert `declName` into the `ToCanonicalM` definitions, with the correct type and value. -/
  partial def define (declName : Name) (settings : Settings) (force := false) : ToCanonicalM ConstantInfo := do
    let shouldDefine := force || match (←get).find? declName with
    | some decl => decl.shouldReplace && settings.depth == 0
    | none => settings.depth < 3

    let env ← getEnv
    let decl := (env.find? declName).getD (panic! s!"define: constant {declName} not found")

    if shouldDefine then
      modify (fun x =>
        x.insert declName (((x.find? declName).map (fun defn => { defn with shouldReplace := false })).getD {})
      )

      let defineType := force || (settings.depth == 0 && !Lean.isClass env declName && ((env.getProjectionFnInfo? declName).isSome || (← includeType decl)))

      -- Consider admitting equational theorems as reduction rules.
      if settings.simp && defineType then
        if let some ⟨valid, rule⟩ := ← eqnRule #[decl.name.toString] decl.type settings then
          if valid && !(← isRflTheorem decl.name) then
            if let some g' := addConstraint rule.lhs rule.rhs (← get) then
              let c := rule.lhs.head.toName
              if let some defn := g'.find? c then
                if !cyclic g' then
                  set (g'.insert c { defn with rules := defn.rules.push rule })
                  return decl

      let type ← if defineType then pure (some (← toTyp decl.type settings)) else pure none

      let irrelevant ← match decl with
      | .recInfo _ => pure false
      | _ => pure ((!Lean.isAuxRecursor env decl.name) && isProp decl.type)

      let rules ← if ← Lean.isIrreducible declName then pure #[] else
        if let some hard_code ← getHardCode declName then
          hard_code.define.forM fun name => do let _ ← define name settings
          let simpnf := (hard_code.simpnf.map toString).toArray
          hard_code.rules.toArray.mapM fun eqn => do
            pure (((← eqnRule (simpnf.push eqn.toString) (← getConstInfo eqn).type settings).getD (panic! "invalid hard code rule")).2)
        else match env.getProjectionFnInfo? declName with
          | some info =>
            let _ ← define info.ctorName settings
            pure #[projRule declName.toString info (info.ctorName.toString) (← getConstInfoCtor info.ctorName) (← forallArity decl.type)]
          | none => match decl with
            | .recInfo info => do
              info.rules.toArray.mapM (λ r => do
                let type ← inferType r.rhs
                let term ← toTerm r.rhs type settings (← forallArity type)
                pure (recRule declName info r.ctor (← getConstInfoCtor r.ctor) term))
            | .inductInfo info =>
              info.ctors.forM fun ctor => do let _ ← define ctor settings

              let _ ← define `False { depth := 1, simp := false }
              let _ ← define `Eq { depth := 1, simp := false }
              let rules ← reduceCtorEqRules decl.name info
              modify (fun x =>
                let defn := (x.find? `Eq).getD (panic! "define: Eq not found after defining")
                let defn := { defn with rules := defn.rules ++ rules }
                (addConstraints rules (x.replace `Eq defn)).getD (panic! "define: ctorEqRules nonterminating")
              )

              match getStructureInfo? env declName with
              | some info => info.fieldInfo.forM fun field => do let _ ← define field.projFn settings
              | none => let _ ← define (mkRecName declName) settings
              pure #[]
            | .defnInfo info =>
              -- Use matcher equations or equation compiler where appropriate.
              if ← isMatcher declName then
                let eqns ← Match.getEquationsFor declName
                eqns.eqnNames.mapM fun eqn => do
                  pure ((← eqnRule #[eqn.toString] (← getConstInfo eqn).type settings).getD (panic! "invalid equation compiler rule")).2
              else if let some eqns ← getEqnsFor? declName then
                eqns.mapM fun eqn => do
                  pure ((← eqnRule #[eqn.toString] (← getConstInfo eqn).type settings).getD (panic! "invalid equation compiler rule")).2
              else
                let defn ← toTerm info.value decl.type
                  { settings with depth := settings.depth + (if ← includeLetType info.value then 1 else 0) }
                  (← forallArity decl.type)
                pure #[defRule declName.toString defn]
            | _ =>
              pure #[]

      modify (fun x =>
        let defn := (x.find? decl.name).getD (panic! "define: definition not found after defining")
        let defn := { defn with type := type, irrelevant := irrelevant, rules := defn.rules ++ rules, shouldReplace := settings.depth > 0 }
        (addConstraints rules (x.replace decl.name defn)).getD (panic! "define: rules nonterminating")
      )
    pure decl

  /-- Translate an `Expr` into a `Typ`, by collecting the `forallE` bindings and `app` arguments until a head symbol is reached.  -/
  partial def toTyp (e : Expr) (settings : Settings) (params : List Var := []) (paramTypes : List (Option Typ) := []) (defTypes : List (Option Typ) := []) (defs : List Let := []) (args : List Expr := [])
     : ToCanonicalM Typ := do
    let e ← whnf e
    match e with
    | bvar _ => unreachable!
    | fvar fvarId =>
      let decl := (← MonadLCtx.getLCtx).get! fvarId
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody decl.type params defs (← nameString e) args settings (← paramArities decl.type)⟩
    | mvar mvarId =>
      let type ← MVarId.getType mvarId
      modify (·.insert mvarId.name {})
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody type params defs (toString mvarId.name) args settings (← paramArities type)⟩
    | sort _u => pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := "Sort" }⟩
    | const declName _us => do
      let decl ← define declName settings
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody decl.type params defs declName.toString args settings (← paramArities decl.type)⟩
    | app fn arg => toTyp fn settings params paramTypes defTypes defs (arg :: args)
    | lam binderName binderType body binderInfo =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        match args with
        | [] => unreachable!
        | arg :: args =>
          let defn ← toTerm arg binderType settings (← forallArity binderType)
          toTyp (body.instantiate1 fvar) settings params paramTypes (none :: defTypes) (⟨← nameString fvar, ← isProp binderType, #[defRule (← nameString fvar) defn]⟩ :: defs) args
    | forallE binderName binderType body binderInfo =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        toTyp (body.instantiate1 fvar) settings (⟨← nameString fvar, ← isProp binderType⟩ :: params) ((←toTyp binderType settings) :: paramTypes) defTypes defs args
    | letE declName type value body _ =>
      withLetDecl declName type value fun fvar => do
        let defn ← toTerm value type settings (← forallArity type)
        toTyp (body.instantiate1 fvar) settings params paramTypes ((← toTyp type settings) :: defTypes) (⟨← nameString fvar, ← isProp type, #[defRule (← nameString fvar) defn]⟩ :: defs) args
    | lit val => pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, { ← defineLiteral val settings with params := ⟨params.reverse⟩, lets := ⟨defs⟩ }⟩
    | mdata _ expr => toTyp expr settings params paramTypes defTypes defs args
    | proj typeName idx struct => do
      let env ← getEnv
      let fields := getStructureFields env typeName
      let structParams := (←withDefault (whnf (← inferType struct))).getAppArgs
      let declName := Option.get! $ getProjFnForField? env typeName fields[idx]!
      let decl ← define declName settings
      let body ← toBody decl.type params defs declName.toString (structParams.toList ++ (struct :: args)) settings (← paramArities decl.type)
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, body⟩

  /-- When we reach the head symbol, we call `toBody` with its type and `paramArities`.
      This function is responsible for recursively tranlating the arguments and building the resultant `Tm`. -/
  partial def toBody (ty : Expr) (params : List Var) (defs : List Let) (head : String) (args : List Expr) (settings : Settings) (arity : List Nat) (state : Array Tm := #[]) (typeArgs : List Expr := []) : ToCanonicalM Tm := do
    let ty ← whnf ty
    match ty with
    | app fn arg => toBody fn params defs head args settings arity state (arg :: typeArgs)
    | lam binderName binderType body _binderInfo =>
      match typeArgs with
      | [] => unreachable!
      | arg :: typeArgs => do
        withLetDecl binderName binderType arg fun fvar => do
          let defn ← toTerm arg binderType settings (← forallArity binderType)
          toBody (body.instantiate1 fvar) params (⟨← nameString fvar, false, #[defRule (← nameString fvar) defn]⟩ :: defs) head args settings arity state typeArgs
    | forallE binderName binderType body binderInfo =>
      match arity, args with
      | [], arg :: args => pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := (``Pi.f).toString, args := #[
          ← toTerm binderType (mkSort .zero) settings 0,
          ← toTerm (mkLambda binderName binderInfo binderType body) (mkForall binderName binderInfo binderType (mkSort .zero)) settings 1,
          ← toBody (body.instantiate1 arg) [] [] head args settings [] state [],
          ← toTerm arg binderType settings (← forallArity binderType)
        ]}
      | n :: arity, arg :: args =>
        toBody (body.instantiate1 arg) params defs head args settings arity (state.push (← toTerm arg binderType settings n)) typeArgs
      | _, [] =>
        withLocalDecl binderName binderInfo binderType fun fvar => do
            pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := (``Pi.mk).toString, args := #[
              ← toTerm binderType (mkSort .zero) settings 0,
              ← toTerm (body.instantiate1 fvar) (mkSort .zero) settings 0 [⟨← nameString fvar, ← isProp binderType⟩],
              ← toBody (body.instantiate1 fvar) [⟨← nameString fvar, ← isProp binderType⟩] [] head (fvar :: args) settings arity state []
            ]}
    | letE declName type value body _ =>
      withLetDecl declName type value fun fvar => do
        let defn ← toTerm value type settings (← forallArity type)
        toBody (body.instantiate1 fvar) params (⟨← nameString fvar, ← isProp type, #[defRule (← nameString fvar) defn]⟩ :: defs) head args settings arity state typeArgs
    | mdata _ expr => toBody expr params defs head args settings arity state typeArgs
    | _ => pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head, args := state}

  /-- Transalate an `Expr` to a `Tm`, by collecting the `lam` bindings and `app` arguments until a head symbol is reached. -/
  partial def toTerm (term : Expr) (type : Expr) (settings : Settings) (arity : Nat) (params : List Var := []) (defs : List Let := []) (args : List Expr := []) (typeArgs : List Expr := []) : ToCanonicalM Tm := do
    let term ← whnf term
    let type ← whnf type
    match term, type, args with
    | _, app fn typeArg, _ => toTerm term fn settings arity params defs args (typeArg :: typeArgs)
    | _, lam binderName binderType body _binderInfo, _ =>
      match typeArgs with
      | [] => unreachable!
      | typeArg :: typeArgs => do
        withLetDecl binderName binderType typeArg fun fvar => do
          let defn ← toTerm typeArg binderType settings (← forallArity typeArg)
          toTerm term (body.instantiate1 fvar) settings arity params (⟨← nameString fvar, ← isProp binderType, #[defRule (← nameString fvar) defn]⟩ :: defs) args typeArgs
    | _, letE declName type value body _, _ =>
      withLetDecl declName type value fun fvar => do
        let defn ← toTerm value type settings (← forallArity type)
        toTerm term (body.instantiate1 fvar) settings arity params (⟨← nameString fvar, ← isProp type, #[defRule (← nameString fvar) defn]⟩ :: defs) args typeArgs
    | _, mdata _ expr, _ => toTerm term expr settings arity params defs args typeArgs
    | lam binderName binderType body _binderInfo, _, arg :: args =>
      withLetDecl binderName binderType arg fun fvar => do
        let defn ← toTerm arg binderType settings (← forallArity binderType)
        toTerm (body.instantiate1 fvar) type settings arity params (⟨← nameString fvar, ← isProp binderType, #[defRule (← nameString fvar) defn]⟩ :: defs) args typeArgs
    | letE declName type value body _, _, _ =>
      withLetDecl declName type value fun fvar => do
        let defn ← toTerm value type settings (← forallArity type)
        toTerm (body.instantiate1 fvar) type settings arity params (⟨← nameString fvar, ← isProp type, #[defRule (← nameString fvar) defn]⟩ :: defs) args typeArgs
    | mdata _ expr, _, _ => toTerm expr type settings arity params defs args typeArgs
    | lam binderName binderType body binderInfo, forallE _binderName' binderType' body' _binderInfo', [] =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        match arity with
        | 0 => pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := (``Pi.mk).toString, args := #[
            ← toTerm binderType' (mkSort .zero) settings 0,
            ← toTerm (body'.instantiate1 fvar) (mkSort .zero) settings 1 [⟨← nameString fvar, ← isProp binderType⟩],
            ← toTerm (body.instantiate1 fvar) (body'.instantiate1 fvar) settings 0 [⟨← nameString fvar, ← isProp binderType⟩]
          ]} -- TODO fvar should always register as arity 1.
        | n + 1 => toTerm (body.instantiate1 fvar) (body'.instantiate1 fvar) settings n (⟨← nameString fvar, ← isProp binderType⟩ :: params) defs args typeArgs
    | _, forallE binderName binderType body binderInfo, _ =>
        withLocalDecl binderName binderInfo binderType fun fvar => do
          match arity with
          | 0 => pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := (``Pi.mk).toString, args := #[
              ← toTerm binderType (mkSort .zero) settings 0,
              ← toTerm (body.instantiate1 fvar) (mkSort .zero) settings 0 [⟨← nameString fvar, ← isProp binderType⟩],
              ← toTerm term (body.instantiate1 fvar) settings 0 [⟨← nameString fvar, ← isProp binderType⟩] [] (args ++ [fvar]) []
            ]}
          | n + 1 => toTerm term (body.instantiate1 fvar) settings n (⟨← nameString fvar, ← isProp binderType⟩ :: params) defs (args ++ [fvar])
    | lam _ _ _ _, const declName _, [] =>
      match (←Lean.getConstInfo declName).value? with
      | none =>
        -- watch out for inifinite loop
        toTerm term (← withDefault (whnf (mkAppN type typeArgs.toArray))) settings arity params defs args
      | some value => toTerm term value settings arity params defs args typeArgs
    | lam _ _ _ _, _, [] => panic! "hidden behind definition"
    | bvar _, _, _ => unreachable!
    | fvar fvarId, _, _ =>
      let decl := (← MonadLCtx.getLCtx).get! fvarId
      toBody decl.type params defs (← nameString term) args settings (← paramArities decl.type)
    | mvar mvarId, _, _ =>
      let type ← MVarId.getType mvarId
      modify (·.insert mvarId.name {})
      toBody type params defs (toString mvarId.name) args settings (← paramArities type)
    | sort _, _, _ => pure { params := ⟨params.reverse⟩, lets := ⟨defs⟩, head := "Sort" }
    | const declName _us, _, _ => do
      let decl ← define declName settings
      toBody decl.type params defs declName.toString args settings (← paramArities decl.type)
    | app fn arg, _, _ => toTerm fn type settings arity params defs (arg :: args) typeArgs
    | forallE binderName binderType body binderInfo, _, _ =>
      let bodyLam := mkLambda binderName binderInfo binderType body
      toTerm (mkAppN (mkConst ``Pi) #[binderType, bodyLam]) type settings arity params defs args typeArgs
    | lit val, _, _ => pure { ← defineLiteral val settings with params := ⟨params.reverse⟩, lets := ⟨defs⟩ }
    | proj typeName idx struct, _, _ => do
      let env ← getEnv
      let fields := getStructureFields env typeName
      let structParams := (← withDefault (whnf (← inferType struct))).getAppArgs
      let declName := Option.get! $ getProjFnForField? env typeName fields[idx]!
      let decl ← define declName settings
      toBody decl.type params defs declName.toString (structParams.toList ++ (struct :: args)) settings (← paramArities decl.type)
end

/-- Determines whether `e` only consists of constants in `constSet`. -/
partial def onlyDefinedConsts (e : Expr) (constSet : HashSet Name) : MetaM Bool := do
  let e ← whnf e
  match e with
  | bvar _ | fvar _ | mvar _ | sort _ | lit _ => pure true
  | const declName _ => pure (constSet.contains declName)
  | app fn arg => do
    onlyDefinedConsts fn constSet <&&> onlyDefinedConsts arg constSet
  | lam binderName binderType body binderInfo => do
    withLocalDecl binderName binderInfo binderType fun fvar => do
      onlyDefinedConsts (body.instantiate1 fvar) constSet
  | forallE binderName binderType body binderInfo => do
    withLocalDecl binderName binderInfo binderType fun fvar => do
      onlyDefinedConsts binderType constSet <&&>
      onlyDefinedConsts (body.instantiate1 fvar) constSet
  | letE declName type value body _ => do
    withLetDecl declName type value fun fvar => do
      onlyDefinedConsts (body.instantiate1 fvar) constSet
  | mdata _ expr => onlyDefinedConsts expr constSet
  | proj typeName _ expr => do
    pure (constSet.contains typeName && (← onlyDefinedConsts expr constSet))

/-- Retrieves the `Origin`s in `trie` consisting only of constants in `constSet`.  -/
partial def getOrigins (constSet : HashSet Name) (trie : Lean.Meta.DiscrTree.Trie SimpTheorem) : Array Origin :=
  match trie with
  | Lean.Meta.DiscrTree.Trie.node vs children =>
    let filtered := children.filter (fun (child : Lean.Meta.DiscrTree.Key × DiscrTree.Trie SimpTheorem) =>
      match child.1 with
      | Lean.Meta.DiscrTree.Key.proj name _ _
      | Lean.Meta.DiscrTree.Key.const name _ => constSet.contains name
      | Lean.Meta.DiscrTree.Key.arrow => false
      | _ => true
    )
    (vs.filterMap (fun x => if x.priority ≥ eval_prio default then some x.origin else none)) ++ filtered.flatMap (fun x => getOrigins constSet x.2)

/-- Converts an `Expr` `e` into a Canonical `Typ`, complete with `Definitions` in the `lets`. -/
def toCanonical (e : Expr) (consts : List Syntax) (pi : Bool) (simp : Bool) : ToCanonicalM Typ := do
  let settings := { depth := 0, simp }
  (← MonadLCtx.getLCtx).forM fun decl => do if !decl.isAuxDecl then
    match ← decl.value?.mapM (fun value => do toTerm value decl.type settings (← forallArity decl.type)) with
    | some term => modify (·.insert (← name decl.toExpr) ⟨none, ← isProp decl.type, #[defRule (← name decl.toExpr).toString term], false, #[]⟩)
    | none => modify (·.insert (← name decl.toExpr) ⟨some (← toTyp decl.type settings), ← isProp decl.type, #[], false, #[]⟩)

  consts.forM (fun stx => match stx with
    | Syntax.ident _ _ val _ => do
      let names ← Lean.resolveGlobalName val
      if h : names ≠ [] then
        let _ := ← define (names.getLast h).1 settings true
      else
        throwErrorAt stx "Not a constant name:{indentD stx}"
      pure ()
    | stx => throwErrorAt stx "Not an identifier:{indentD stx}"
  )
  if pi then let _ := ← define ``Canonical.Pi settings true

  let ⟨paramTypes, defTypes, ⟨params, defs, head, args, _, _⟩⟩ ← toTyp e settings

  -- Proactively search for `simp` lemmas to add as reduction rules.
  if simp then
    let constArray := (← get).toList.toArray.filter (fun ⟨_, defn⟩ => defn.type.isSome)
    let constSet := HashSet.ofArray (constArray.map (·.1))
    let thms ← getSimpTheorems
    let tries := constArray.filterMap (fun x =>
      x.2.type.bind fun typ => thms.post.root.find? (.const x.1 typ.params.size)
    )
    let origins := tries.flatMap (getOrigins constSet)
    let _ ← origins.forM fun origin => do
      if let .decl name _ _ := origin then
        let e := ((← getEnv).find? name |>.getD (panic! s!"simp lemma {name} does not exist.")).type
        if (← onlyDefinedConsts e constSet) && !(← isRflTheorem name) then
          if let some ⟨valid, rule⟩ ← eqnRule #[name.toString] e { depth := 1, simp := false } then
            if valid then
              if let some g' := addConstraint rule.lhs rule.rhs (← get) then
                let c := rule.lhs.head.toName
                if let some defn := g'.find? c then
                  if !cyclic g' then
                    set (g'.insert c { defn with rules := defn.rules.push rule })

  let decls := (← get).toList.toArray.push ⟨Name.mkSimple "Sort", { type := some {codomain := { head := "Sort"}} }⟩
  pure ⟨paramTypes, decls.map (λ ⟨_, t⟩ => t.type) ++ defTypes,
    { params, lets := (decls.map (λ ⟨name, t⟩ => ⟨name.toString false, t.irrelevant, t.rules⟩) ++ defs), head, args }⟩

/-- When translating from Canonical, we associate names in the `Tm` with corresponding Lean `FVarId`s -/
abbrev FromCanonicalM := StateT (AssocList String FVarId) MetaM

/-- Create `n` fresh `LevelMVar`s. -/
def mvarLevels (n : Nat) : FromCanonicalM (List Level) := do
  match n with
  | Nat.zero => pure []
  | Nat.succ m =>
    let fresh ← mkFreshLMVarId
    let l ← mvarLevels m
    pure ((mkLevelMVar fresh) :: l)

/-- Syntax for `simp` and `simpa` calls generated given the `premiseRules` and `goalRules` attribution. -/
def toSyntax (premiseRules: Array String) (goalRules: Array String) : Syntax := Unhygienic.run do
  let premiseRules := premiseRules.toList.toSSet.toList.toArray
  let goalRules := goalRules.toList.toSSet.toList.toArray
  let result ← if premiseRules.isEmpty then `(tacticSeq| exact $(TSyntax.mk .missing)) else
    let cc : Array (TSyntax `ident) := premiseRules.map (fun s => mkIdent s.toName)
    `(tacticSeq| simpa only [$[$cc:ident],*] using $(TSyntax.mk .missing))
  let result ← if goalRules.isEmpty then
    `(term| by $result)
  else do
    let cc : Array (TSyntax `ident) := goalRules.map (fun s => mkIdent s.toName)
    `(term| by simp only [$[$cc:ident],*] <;> $(TSyntax.mk result))
  pure result

mutual
  /-- Builds a lambda expression of type `type` following the parameters of Tm `term`. -/
  partial def toLam (type : Expr) (term : Tm) (typeArgs : List Expr) (paramIndex : Nat) : FromCanonicalM Expr := do
    let type ← whnf type
    match type with
    | app fn arg => toLam fn term (arg :: typeArgs) paramIndex
    | lam binderName binderType body _binderInfo =>
      match typeArgs with
      | [] => unreachable!
      | d :: args' => do
        withLetDecl binderName binderType d fun fvar => toLam (body.instantiate1 fvar) term args' paramIndex
    | forallE binderName binderType body binderInfo =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        modify (·.insert term.params[paramIndex]!.1 fvar.fvarId!)
        pure $ mkLambda binderName binderInfo binderType $ (←toLam (body.instantiate1 fvar) term typeArgs (paramIndex + 1)).abstract #[fvar]
    | letE binderName binderType value body _nonDep =>
      withLetDecl binderName binderType value fun fvar =>
        toLam (body.instantiate1 fvar) term typeArgs paramIndex
    | _ =>
      -- if there are non-rfl `premiseRules` or `goalRules`, generate `simp`/`simpa` syntax.
      let premiseRules := if ← term.premiseRules.allM (fun s => do isRflTheorem s.toName) then #[] else term.premiseRules
      let goalRules := if ← term.goalRules.allM (fun s => do isRflTheorem s.toName) then #[] else term.goalRules

      if (!premiseRules.isEmpty || !goalRules.isEmpty) then
        return .mdata (KVMap.empty.insert `canonical (.ofSyntax (toSyntax premiseRules goalRules)))
          (←toLam type { term with premiseRules := #[], goalRules := #[] } typeArgs paramIndex)

      do match (←get).find? term.head with
        | none =>
          if term.head = "Sort" then pure (mkSort (mkLevelMVar (← mkFreshLMVarId))) else
          match term.head.toNat? with
          | some n => pure (mkRawNatLit n)
          | none =>
            let constName := term.head.toName
            match (← getEnv).find? constName with
            | none =>
              let name := ((term.head.dropWhile (fun x => x != ';')).drop 1).takeWhile (fun x => x.isAlphanum)
              mkFreshExprMVar (some (mkAppN type typeArgs.toArray)) (userName := name.toName)
            | some decl => toApp decl.type (mkConst constName (←mvarLevels decl.numLevelParams)) term.args.toList 0 []
        | some fvarId => toApp ((← MonadLCtx.getLCtx).get! fvarId).type (mkFVar fvarId) term.args.toList 0 []

  /-- Builds an application of type `type` following the `args` -/
  partial def toApp (type : Expr) (spine : Expr) (args : List Tm) (argsIndex : Nat) (typeArgs : List Expr) : FromCanonicalM Expr := do
    let type ← whnf type
    match type with
    | app fn arg => toApp fn spine args argsIndex (arg :: typeArgs)
    | lam binderName binderType body _binderInfo =>
      match typeArgs with
      | [] => unreachable!
      | d :: args' => do
        withLetDecl binderName binderType d fun fvar => toApp (body.instantiate1 fvar) spine args argsIndex args'
    | forallE _binderName binderType body _binderInfo =>
      let arg ← toLam binderType args[argsIndex]! [] 0
      toApp (body.instantiate1 arg) (mkApp spine arg) args (argsIndex + 1) typeArgs
    | letE binderName binderType value body _nonDep =>
      withLetDecl binderName binderType value fun fvar => toApp (body.instantiate1 fvar) spine args argsIndex typeArgs
    | _ => pure spine
end

/-- Turn instances of `Pi` wrapper into native `forallE`. -/
partial def dePi (e : Expr) : Expr :=
  if e.isAppOf ``Pi then
    let args := e.getAppArgs.map dePi
    let lam := args[1]!
    (mkForall lam.bindingName! lam.bindingInfo! lam.bindingDomain! lam.bindingBody!)
  else if e.isAppOf ``Pi.f then
    let args := e.getAppArgs.map dePi
    (mkApp (args[2]!) (args[3]!))
  else if e.isAppOf ``Pi.mk then
    dePi (e.getArg! 2)
  else
    match e with
    | app fn arg => mkApp (dePi fn) (dePi arg)
    | lam binderName binderType body binderInfo => mkLambda binderName binderInfo (dePi binderType) (dePi body)
    | letE binderName binderType value body nonDep => mkLet binderName (dePi binderType) (dePi value) (dePi body) (nonDep := nonDep)
    | _ => e

/-- Lean's default unfolding predicate copied from `Lean.Meta.GetUnfoldableConst`. -/
def canUnfoldDefault (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  match cfg.transparency with
  | .all => return true
  | .default => return !(← isIrreducible info.name)
  | m =>
    if (← isReducible info.name) then
      return true
    else if m == .instances && isGlobalInstance (← getEnv) info.name then
      return true
    else
      return false

/-- Custom unfolding predicate that unfolds definitions whose body is a `forallE`. -/
def canUnfold (e : Expr) : CoreM Bool := do
  match e with
  | app body _ | lam _ _ body _ | letE _ _ _ body _ | mdata _ body => canUnfold body
  | forallE _ _ _ _ => pure true
  | _ => pure false

structure CanonicalConfig where
  /-- Canonical produces `count` proofs. -/
  count: USize := 1
  /-- Provides `(A → B) : Sort` as an axiom to Canonical. -/
  pi: Bool := false
  debug: Bool := false
  /-- Opens the refinement UI. -/
  refine: Bool := false
  simp: Bool := true

declare_config_elab canonicalConfig CanonicalConfig

/-- A version of `Core.checkInterrupted` that does not crash. -/
def checkInterrupted : CoreM Bool := do
  if let some tk := (← read).cancelTk? then pure (← tk.isSet)
  else pure false

end Canonical

open Canonical
open Lean Elab Meta Tactic

def applyOptions : Options → Options :=
  (pp.proofs.set · true |>
  (pp.motives.all.set · true |>
  (pp.coercions.set · false |>
  (pp.unicode.fun.set · true))))

structure RpcData where
  goal: Expr
  lctx: LocalContext
  width: Nat
  indent: Nat
  column: Nat
deriving TypeName

structure InsertParams where
  rpcData : Server.WithRpcRef RpcData
  /-- Position of our widget instance in the Lean file. -/
  pos : Lsp.Position
  range: Lsp.Range
deriving Server.RpcEncodable

open Server RequestM in
/-- Gets the String to be inserted into the document, for the refinement widget. -/
@[server_rpc_method]
def getRefinementStr (params : InsertParams) : RequestM (RequestTask String) :=
  withWaitFindSnapAtPos params.pos fun snap => do
    runTermElabM snap do
      let data := params.rpcData.val
      let lctx := data.lctx

      withLCtx' lctx do
        let map ← lctx.foldlM (fun map decl => do
          if Lean.LocalDecl.isAuxDecl decl then pure map else pure (map.insert (← nameString (mkFVar decl.fvarId)) decl.fvarId)) {}

        MonadWithOptions.withOptions applyOptions do
          let expr := dePi (← (toLam data.goal (← getRefinement) [] 0).run' map)
          let tm ← Lean.Meta.Tactic.TryThis.delabToRefinableSyntax expr
          let stx ← `(tactic| refine $tm)
          let fmt ← Lean.PrettyPrinter.ppCategory `tactic stx
          let str := Std.Format.pretty fmt data.width data.indent data.column
          pure str

/-- The widget for the refinement UI. -/
@[widget_module]
def refineWidget : Widget.Module where
  javascript := include_str "refine.js"

open PrettyPrinter Delaborator SubExpr in
@[delab mdata.canonical]
def delabCanonical : Delab := do
  match ← getExpr with
  | .mdata map _ =>
    let result ← (map.getSyntax `canonical).replaceM (fun x =>
      if x.isMissing then withMDataExpr delab else pure none)
    pure (TSyntax.mk result)
  | _ => throwError "delabCanonical called on non-mdata"

syntax canonicalRuleSeq := " [" withoutPosition(term,*,?) "]"
/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:Parser.Tactic.optConfig s:(canonicalRuleSeq)? : tactic => do
  let argList ← match s with
  | some t => match t with
    | `(canonicalRuleSeq| [$args,*]) => pure args.getElems.raw.toList
    | _ => Elab.throwUnsupportedSyntax
  | none => pure []

  Meta.withCanUnfoldPred (λ config info => do pure ((← canUnfoldDefault config info) || (← canUnfold info.value!))) $ withReducibleAndInstances $ withMainContext do
    -- let start ← Std.Time.Timestamp.now
    let config ← canonicalConfig config

    let goal ← getMainTarget
    let type ← toCanonical goal argList config.pi config.simp |>.run' default

    let lctx ← MonadLCtx.getLCtx
    let map ← lctx.foldlM (fun map decl => do
      if Lean.LocalDecl.isAuxDecl decl then pure map else pure (map.insert (← nameString (mkFVar decl.fvarId)) decl.fvarId)) {}

    if config.refine then
      let _ ← refine type
      Elab.admitGoal (← getMainGoal)
      let fileMap ← getFileMap
      let strRange := (← getRef).getRange?.getD (panic! "No range found!")
      let range := fileMap.utf8RangeToLspRange strRange
      let width := Lean.Meta.Tactic.TryThis.getInputWidth (← getOptions)
      let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn fileMap strRange
      Lean.Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef)
        (props := do
          let rpcData ← Server.RpcEncodable.rpcEncode (Server.WithRpcRef.mk (RpcData.mk goal lctx width indent column))
          pure (Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)]))
      return

    let timeout := match timeout_syntax with
    | some n => n.getNat
    | none => 10

    if config.debug then
      Elab.admitGoal (← getMainGoal)
      let _ ← save_to_file type "debug.json"
      dbg_trace type
      return

    Core.checkInterrupted
    let task ← IO.asTask (prio := Task.Priority.dedicated)
      (canonical type (UInt64.ofNat timeout) config.count)
    while !(← IO.hasFinished task) do
      if ← checkInterrupted then
        IO.cancel task
        Core.checkInterrupted
      IO.sleep 10

    let result ← IO.ofExcept task.get

    let proofs ← result.terms.mapM fun term => do
      pure (dePi (← (toLam goal term [] 0).run' map))

    MonadWithOptions.withOptions applyOptions do
      if proofs.isEmpty then
        match s with
        | some _ =>
          match timeout_syntax with
          | some _ => throwError "No proof found."
          | none => throwError "No proof found. Change timeout to `n` with `canonical n`"
        | none => throwError "No proof found. Supply constant symbols with `canonical [name, ...]`"
      else
        Elab.admitGoal (← getMainGoal)
        if h : proofs.size = 1 then
          Meta.Tactic.TryThis.addExactSuggestion (← getRef) proofs[0]
        else
          Meta.Tactic.TryThis.addExactSuggestions (← getRef) proofs
    -- dbg_trace ←start.since
    -- dbg_trace "{←start.since}\t{result.attempted_resolutions}\t{result.successful_resolutions}\t{result.steps}\t{result.last_level_steps}\t{result.branching}\t{size proof}"
