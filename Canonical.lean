import Lean
-- import Std.Time.DateTime.Timestamp

namespace Canonical

/-- A variable with a `name`, and whether it is proof `irrelevant` (unused). -/
structure Var where
  name: String
  irrelevant: Bool
deriving Inhabited

mutual
  /-- The value of a let declaration, which can be a term,
      custom reduction behavior (like recursor), or opaque. -/
  inductive Value where
  | definition : (term : Tm) → Value
  | constructor : (type : String) → (index : USize) → (argsStart : USize) → Value
  | recursor : (type : String) → (rules : Array Tm) → (shared : USize) → (major : USize) → Value
  | projection : (type : String) → (index : USize) → (major : USize) → Value
  | opaque : Value
  deriving Inhabited

  /-- A let declaration, with a name and value. -/
  structure Let where
    name: String
    irrelevant: Bool
    value: Value
  deriving Inhabited

  /-- A term is an n-ary, β-normal, η-long λ expression:
      `λ params lets . head args` -/
  structure Tm where
    params: Array Var := #[]
    lets: Array Let := #[]
    head: String
    args: Array Tm := #[]
  deriving Inhabited
end

/-- A type is an n-ary Π-type: `Π params lets . codomain` -/
structure Typ where
  params: Array (Option Typ)
  lets: Array (Option Typ)
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

/-- Generate terms of a given type, with given timeout, desired count, `synth` and `debug` flags -/
@[never_extract, extern "canonical"] opaque canonical : @& Typ → UInt64 → USize → Bool → Bool → IO CanonicalResult

/-- Start a server with the refinement UI on the given type. -/
@[never_extract, extern "refine"] opaque refine : @& Typ → Bool → IO Unit

/-- Obtains the current term from the refinement UI. -/
@[never_extract, extern "get_refinement"] opaque getRefinement : IO Tm

/-- Some Lean Π-types cannot be converted into Canonical Π-types,
    and are instead converted into this structure. -/
structure Pi (A : Type u) (B : A → Type v) where
  f : (a : A) → B a

open Std Lean Elab.Tactic Expr Meta

/-- `define` is a list of names that should be defined
    if this HardCode is triggered -/
structure HardCode where
  define: List Name

/-- Rather than recursively unfolding definitions, `HARD_CODE` overrides
    the definitions introduced by a given symbol. -/
def HARD_CODE : Std.HashMap (Name × Name) HardCode := .ofList [
    ⟨⟨`Mathlib.Data.Real.Basic, `Real⟩, ⟨[]⟩⟩
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
  value: Value := Value.opaque
  shouldReplace: Bool := false

/- def print_force (s : String) : IO Unit := do
  let handle ← IO.FS.Handle.mk "output.txt" IO.FS.Mode.append
  handle.putStrLn s
  handle.flush -/

/-- When translating to Canonical, we maintain a state of translated constant symbols. -/
abbrev ToCanonicalM := StateT (AssocList Name Definition) MetaM

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
    let decl := (← getEnv).find? declName |>.get!
    isOpaque decl
  | _ => pure false

/- If true, gives the surrounding definition a type. -/
def includeType (info : ConstantInfo) : ToCanonicalM Bool := do
  if ← Lean.isIrreducible info.name then pure true else
  match info with
  | .ctorInfo info => pure !(isClass (← getEnv) info.induct)
  | .defnInfo info => pure <| !(isAuxRecursor (← getEnv) info.name) && (← includeLetType info.value)
  | _ => pure true

mutual
  /-- At present, only small natural numbers are converted into a `Tm`. Other literals are `opaque`. -/
  partial def defineLiteral (val : Literal) (insideLet : Nat) : ToCanonicalM String := do
    let str := match val with | .natVal n => toString n | .strVal s => s!"\"{s}\""
    let name := Name.mkSimple str
    let type ← if insideLet > 0 then pure none else pure (some (← toTyp val.type insideLet))
    if !(←get).contains name then do
      match val with
      | .natVal n =>
        modify (·.insert name ⟨if n <= 5 then none else type, false, if n <= 5 then Value.definition (natToTerm n) else Value.opaque, insideLet > 0⟩)
      | .strVal _ =>
        modify (·.insert name ⟨type, false, Value.opaque, insideLet > 0⟩)
    pure str

  /-- Insert `declName` into the `ToCanonicalM` definitions, with the correct type and value. -/
  partial def define (declName : Name) (insideLet : Nat) (force := false) : ToCanonicalM ConstantInfo := do
    let shouldDefine := force || match (←get).find? declName with
    | some decl => decl.shouldReplace && insideLet == 0
    | none => insideLet < 3

    let env ← getEnv
    let decl := env.find? declName |>.get!

    if shouldDefine then
      modify (·.insert declName {})

      let irrelevant ← match decl with
      | .recInfo _ => pure false
      | _ => pure ((!Lean.isAuxRecursor env decl.name) && isProp decl.type)

      let value ← if ← Lean.isIrreducible declName then pure Value.opaque else
        if let some hard_code ← getHardCode declName then
          hard_code.define.forM fun name => do let _ ← define name insideLet
          pure Value.opaque
        else match env.getProjectionFnInfo? declName with
          | some info =>
            let name := Option.get! (env.getProjectionStructureName? declName)
            pure (Value.projection name.toString ⟨info.i⟩ ⟨info.numParams⟩)
          | none => match decl with
            | .ctorInfo ctor =>
              let induct ← getConstInfoInduct ctor.induct
              pure (Value.constructor induct.name.toString ⟨ctor.cidx⟩ ⟨induct.numParams⟩)
            | .recInfo info => do
              let rules ← (info.rules.mapM (λ r => do
                let type ← inferType r.rhs
                toTerm r.rhs type insideLet (← forallArity type)))
              pure (Value.recursor info.getMajorInduct.toString ⟨rules⟩ ⟨info.getFirstIndexIdx⟩ ⟨info.getMajorIdx⟩)
            | .inductInfo info =>
              info.ctors.forM fun ctor => do let _ ← define ctor insideLet
              match getStructureInfo? env declName with
              | some info => info.fieldInfo.forM fun field => do let _ ← define field.projFn insideLet
              | none => let _ ← define (mkRecName declName) insideLet
              pure Value.opaque
            | .defnInfo info => pure (Value.definition (← toTerm info.value decl.type (insideLet + (if ← includeLetType info.value then 1 else 0)) (← forallArity decl.type)))
            | _ => pure Value.opaque

      let defineType := force || (insideLet == 0 && !Lean.isClass env declName && ((env.getProjectionFnInfo? declName).isSome || (← includeType decl)))
      let type ← if defineType then pure (some (← toTyp decl.type insideLet)) else pure none

      modify (·.insert declName ⟨type, irrelevant, value, insideLet > 0⟩)
    pure decl

  /-- Translate an `Expr` into a `Typ`, by collecting the `forallE` bindings and `app` arguments until a head symbol is reached.  -/
  partial def toTyp (e : Expr) (insideLet : Nat) (params : List Var := []) (paramTypes : List (Option Typ) := []) (defTypes : List (Option Typ) := []) (defs : List Let := []) (args : List Expr := [])
     : ToCanonicalM Typ := do
    let e ← whnf e
    match e with
    | bvar _ => unreachable!
    | fvar fvarId =>
      let decl := (← MonadLCtx.getLCtx).get! fvarId
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody decl.type params defs (← nameString e) args insideLet (← paramArities decl.type)⟩
    | mvar mvarId =>
      let type ← MVarId.getType mvarId
      modify (·.insert mvarId.name {})
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody type params defs (toString mvarId.name) args insideLet (← paramArities type)⟩
    | sort _u => pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ⟨⟨params.reverse⟩, ⟨defs⟩, "Sort", #[]⟩⟩
    | const declName _us => do
      let decl ← define declName insideLet
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ← toBody decl.type params defs declName.toString args insideLet (← paramArities decl.type)⟩
    | app fn arg => toTyp fn insideLet params paramTypes defTypes defs (arg :: args)
    | lam binderName binderType body binderInfo =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        match args with
        | [] => unreachable!
        | arg :: args => toTyp (body.instantiate1 fvar) insideLet params paramTypes (none :: defTypes) (⟨← nameString fvar, ← isProp binderType, Value.definition (← toTerm arg binderType insideLet (← forallArity binderType))⟩ :: defs) args
    | forallE binderName binderType body binderInfo =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        toTyp (body.instantiate1 fvar) insideLet (⟨← nameString fvar, ← isProp binderType⟩ :: params) ((←toTyp binderType insideLet) :: paramTypes) defTypes defs args
    | letE declName type value body _ =>
      withLetDecl declName type value fun fvar => do
        toTyp (body.instantiate1 fvar) insideLet params paramTypes ((← toTyp type insideLet) :: defTypes) (⟨← nameString fvar, ← isProp type, Value.definition (← toTerm value type insideLet (← forallArity type))⟩ :: defs) args
    | lit val => pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, ⟨⟨params.reverse⟩, ⟨defs⟩, ← defineLiteral val insideLet, #[]⟩⟩
    | mdata _ expr => toTyp expr insideLet params paramTypes defTypes defs args
    | proj typeName idx struct => do
      let env ← getEnv
      let fields := getStructureFields env typeName
      let structParams := (←withDefault (whnf (← inferType struct))).getAppArgs
      let declName := Option.get! $ getProjFnForField? env typeName fields[idx]!
      let decl ← define declName insideLet
      let body ← toBody decl.type params defs declName.toString (structParams.toList ++ (struct :: args)) insideLet (← paramArities decl.type)
      pure ⟨⟨paramTypes.reverse⟩, ⟨defTypes⟩, body⟩

  /-- When we reach the head symbol, we call `toBody` with its type and `paramArities`.
      This function is responsible for recursively tranlating the arguments and building the resultant `Tm`. -/
  partial def toBody (ty : Expr) (params : List Var) (defs : List Let) (head : String) (args : List Expr) (insideLet : Nat) (arity : List Nat) (state : Array Tm := #[]) (typeArgs : List Expr := []) : ToCanonicalM Tm := do
    let ty ← whnf ty
    match ty with
    | app fn arg => toBody fn params defs head args insideLet arity state (arg :: typeArgs)
    | lam binderName binderType body _binderInfo =>
      match typeArgs with
      | [] => unreachable!
      | arg :: typeArgs => do
        withLetDecl binderName binderType arg fun fvar => do
          toBody (body.instantiate1 fvar) params (⟨← nameString fvar, false, Value.definition (← toTerm arg binderType insideLet (← forallArity binderType))⟩ :: defs) head args insideLet arity state typeArgs
    | forallE binderName binderType body binderInfo =>
      match arity, args with
      | [], arg :: args => pure ⟨⟨params.reverse⟩, ⟨defs⟩, (``Pi.f).toString, #[
          ← toTerm binderType (mkSort .zero) insideLet 0,
          ← toTerm (mkLambda binderName binderInfo binderType body) (mkForall binderName binderInfo binderType (mkSort .zero)) insideLet 1,
          ← toBody (body.instantiate1 arg) [] [] head args insideLet [] state [],
          ← toTerm arg binderType insideLet (← forallArity binderType)
        ]⟩
      | n :: arity, arg :: args =>
        toBody (body.instantiate1 arg) params defs head args insideLet arity (state.push (← toTerm arg binderType insideLet n)) typeArgs
      | _, [] =>
        withLocalDecl binderName binderInfo binderType fun fvar => do
            pure ⟨⟨params.reverse⟩, ⟨defs⟩, (``Pi.mk).toString, #[
              ← toTerm binderType (mkSort .zero) insideLet 0,
              ← toTerm (body.instantiate1 fvar) (mkSort .zero) insideLet 0 [⟨← nameString fvar, ← isProp binderType⟩],
              ← toBody (body.instantiate1 fvar) [⟨← nameString fvar, ← isProp binderType⟩] [] head (fvar :: args) insideLet arity state []
            ]⟩
    | letE declName type value body _ =>
      withLetDecl declName type value fun fvar => do
        toBody (body.instantiate1 fvar) params (⟨← nameString fvar, ← isProp type, Value.definition (← toTerm value type insideLet (← forallArity type))⟩ :: defs) head args insideLet arity state typeArgs
    | mdata _ expr => toBody expr params defs head args insideLet arity state typeArgs
    | _ => pure ⟨⟨params.reverse⟩, ⟨defs⟩, head, state⟩

  /-- Transalate an `Expr` to a `Tm`, by collecting the `lam` bindings and `app` arguments until a head symbol is reached. -/
  partial def toTerm (term : Expr) (type : Expr) (insideLet : Nat) (arity : Nat) (params : List Var := []) (defs : List Let := []) (args : List Expr := []) (typeArgs : List Expr := []) : ToCanonicalM Tm := do
    let term ← whnf term
    let type ← whnf type
    match term, type, args with
    | _, app fn typeArg, _ => toTerm term fn insideLet arity params defs args (typeArg :: typeArgs)
    | _, lam binderName binderType body _binderInfo, _ =>
      match typeArgs with
      | [] => unreachable!
      | typeArg :: typeArgs => do
        withLetDecl binderName binderType typeArg fun fvar => do
          toTerm term (body.instantiate1 fvar) insideLet arity params (⟨← nameString fvar, ← isProp binderType, Value.definition (← toTerm typeArg binderType insideLet (← forallArity typeArg))⟩ :: defs) args typeArgs
    | _, letE declName type value body _, _ =>
      withLetDecl declName type value fun fvar => do
        toTerm term (body.instantiate1 fvar) insideLet arity params (⟨← nameString fvar, ← isProp type, Value.definition (← toTerm value type insideLet (← forallArity type))⟩ :: defs) args typeArgs
    | _, mdata _ expr, _ => toTerm term expr insideLet arity params defs args typeArgs
    | lam binderName binderType body _binderInfo, _, arg :: args =>
      withLetDecl binderName binderType arg fun fvar => do
        toTerm (body.instantiate1 fvar) type insideLet arity params (⟨← nameString fvar, ← isProp binderType, Value.definition (← toTerm arg binderType insideLet (← forallArity binderType))⟩ :: defs) args typeArgs
    | letE declName type value body _, _, _ =>
      withLetDecl declName type value fun fvar => do
        toTerm (body.instantiate1 fvar) type insideLet arity params (⟨← nameString fvar, ← isProp type, Value.definition (← toTerm value type insideLet (← forallArity type))⟩ :: defs) args typeArgs
    | mdata _ expr, _, _ => toTerm expr type insideLet arity params defs args typeArgs
    | lam binderName binderType body binderInfo, forallE _binderName' binderType' body' _binderInfo', [] =>
      withLocalDecl binderName binderInfo binderType fun fvar => do
        match arity with
        | 0 => pure ⟨⟨params.reverse⟩, ⟨defs⟩, (``Pi.mk).toString, #[
            ← toTerm binderType' (mkSort .zero) insideLet 0,
            ← toTerm (body'.instantiate1 fvar) (mkSort .zero) insideLet 1 [⟨← nameString fvar, ← isProp binderType⟩],
            ← toTerm (body.instantiate1 fvar) (body'.instantiate1 fvar) insideLet 0 [⟨← nameString fvar, ← isProp binderType⟩]
          ]⟩
        | n + 1 => toTerm (body.instantiate1 fvar) (body'.instantiate1 fvar) insideLet n (⟨← nameString fvar, ← isProp binderType⟩ :: params) defs args typeArgs
    | _, forallE binderName binderType body binderInfo, _ =>
        withLocalDecl binderName binderInfo binderType fun fvar => do
          match arity with
          | 0 => pure ⟨⟨params.reverse⟩, ⟨defs⟩, (``Pi.mk).toString, #[
              ← toTerm binderType (mkSort .zero) insideLet 0,
              ← toTerm (body.instantiate1 fvar) (mkSort .zero) insideLet 0 [⟨← nameString fvar, ← isProp binderType⟩],
              ← toTerm term (body.instantiate1 fvar) insideLet 0 [⟨← nameString fvar, ← isProp binderType⟩] [] (args ++ [fvar]) []
            ]⟩
          | n + 1 => toTerm term (body.instantiate1 fvar) insideLet n (⟨← nameString fvar, ← isProp binderType⟩ :: params) defs (args ++ [fvar])
    | lam _ _ _ _, const declName _, [] =>
      match (←Lean.getConstInfo declName).value? with
      | none =>
        -- watch out for inifinite loop
        toTerm term (← withDefault (whnf (mkAppN type typeArgs.toArray))) insideLet arity params defs args
      | some value => toTerm term value insideLet arity params defs args typeArgs
    | lam _ _ _ _, _, [] => panic! "hidden behind definition"
    | bvar _, _, _ => unreachable!
    | fvar fvarId, _, _ =>
      let decl := (← MonadLCtx.getLCtx).get! fvarId
      toBody decl.type params defs (← nameString term) args insideLet (← paramArities decl.type)
    | mvar mvarId, _, _ =>
      let type ← MVarId.getType mvarId
      modify (·.insert mvarId.name {})
      toBody type params defs (toString mvarId.name) args insideLet (← paramArities type)
    | sort _, _, _ => pure ⟨⟨params.reverse⟩, ⟨defs⟩, "Sort", #[]⟩
    | const declName _us, _, _ => do
      let decl ← define declName insideLet
      toBody decl.type params defs declName.toString args insideLet (← paramArities decl.type)
    | app fn arg, _, _ => toTerm fn type insideLet arity params defs (arg :: args) typeArgs
    | forallE binderName binderType body binderInfo, _, _ =>
      let bodyLam := mkLambda binderName binderInfo binderType body
      toTerm (mkAppN (mkConst ``Pi) #[binderType, bodyLam]) type insideLet arity params defs args typeArgs
    | lit val, _, _ => pure ⟨⟨params.reverse⟩, ⟨defs⟩, ← defineLiteral val insideLet, #[]⟩
    | proj typeName idx struct, _, _ => do
      let env ← getEnv
      let fields := getStructureFields env typeName
      let structParams := (← withDefault (whnf (← inferType struct))).getAppArgs
      let declName := Option.get! $ getProjFnForField? env typeName fields[idx]!
      let decl ← define declName insideLet
      toBody decl.type params defs declName.toString (structParams.toList ++ (struct :: args)) insideLet (← paramArities decl.type)
end

/-- Converts an `Expr` `e` into a Canonical `Typ`, complete with `Definitions` in the `lets`. -/
def toCanonical (e : Expr) (consts : List Syntax) (pi : Bool) : ToCanonicalM Typ := do
  (← MonadLCtx.getLCtx).forM fun decl => do if !decl.isAuxDecl then
    match ← decl.value?.mapM (fun value => do toTerm value decl.type 0 (← forallArity decl.type)) with
    | some term => modify (·.insert (← name decl.toExpr) ⟨none, ← isProp decl.type, Value.definition term, false⟩)
    | none => modify (·.insert (← name decl.toExpr) ⟨some (← toTyp decl.type 0), ← isProp decl.type, Value.opaque, false⟩)

  consts.forM (fun stx => match stx with
    | Syntax.ident _ _ val _ => do
      let names ← Lean.resolveGlobalName val
      if h : names ≠ [] then
        let _ := ← define (names.getLast h).1 0 true
      else
        throwErrorAt stx "Not a constant name:{indentD stx}"
      pure ()
    | stx => throwErrorAt stx "Not an identifier:{indentD stx}"
  )
  if pi then let _ := ← define ``Canonical.Pi 0 true

  let ⟨paramTypes, defTypes, ⟨params, defs, head, args⟩⟩ ← toTyp e 0
  let decls := (← get).toList.toArray.push ⟨Name.mkSimple "Sort", ⟨some ⟨#[], #[], ⟨#[], #[], "Sort", #[]⟩⟩, false, Value.opaque, false⟩⟩
  pure ⟨paramTypes, decls.map (λ ⟨_, t⟩ => t.type) ++ defTypes,
    ⟨params, (decls.map (λ ⟨name, t⟩ => ⟨name.toString false, t.irrelevant, t.value⟩) ++ defs), head, args⟩⟩

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
      do match (←get).find? term.head with
        | none =>
          if term.head = "Sort" then pure (mkSort (mkLevelMVar (← mkFreshLMVarId))) else
          match term.head.toNat? with
          | some n => pure (mkRawNatLit n)
          | none =>
            let constName := term.head.toName
            match (← getEnv).find? constName with
            | none =>
              let name := ((term.head.dropWhile (fun x => x != '?')).drop 1).takeWhile (fun x => x.isAlphanum)
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
  /-- Guarantees completeness with respect to iota reduction. -/
  synth: Bool := false
  /-- Provides `(A → B) : Sort` as an axiom to Canonical. -/
  pi: Bool := false
  debug: Bool := false
  /-- Opens the refinement UI. -/
  refine: Bool := false

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
    if config.synth then
      throwError "`synth` is currently an unstable feature."

    let goal ← getMainTarget
    let type ← toCanonical goal argList config.pi |>.run' default

    let lctx ← MonadLCtx.getLCtx
    let map ← lctx.foldlM (fun map decl => do
      if Lean.LocalDecl.isAuxDecl decl then pure map else pure (map.insert (← nameString (mkFVar decl.fvarId)) decl.fvarId)) {}

    if config.refine then
      let _ ← refine type config.synth
      Elab.admitGoal (← getMainGoal)
      let fileMap ← getFileMap
      let strRange := (← getRef).getRange?.get!
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
      dbg_trace type
    Core.checkInterrupted
    let task ← IO.asTask (prio := Task.Priority.dedicated)
      (canonical type (UInt64.ofNat timeout) config.count config.synth config.debug)
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
