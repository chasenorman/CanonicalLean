module

import Lean
public import Lean.Data.AssocList
public import Canonical.Basic
public import Canonical.Util
public import Canonical.Monomorphize.Basic
import Canonical.Destruct.Basic
import Canonical.Symbols

open Lean Meta Expr Std Monomorphize

namespace Canonical

public section

/-- Definition of a symbol during translation, to be converted into a `Decl`. -/
structure Definition where
  /-- `.undef` corresponds to a definition without translated type,
      but may acquire one as the translation progresses. -/
  type: LOption Canonical.Expr
  arity: Arity
  equations: Array Rule := #[]
  neighbors: HashSet String := {}
deriving Inhabited

/-- Whether we are translating a premise or a goal. -/
inductive Polarity where
| premise
| goal

/-- The opposite polarity. -/
def flip : Polarity → Polarity
| .premise => .goal
| .goal => .premise

/-- Reader data for `ToCanonical`. -/
structure Context where
  arities: HashMap FVarId Arity
  /-- All `define` invocations will set `.undef` type. -/
  noTypes: Bool := false
  config: Config
  polarity: Polarity := .goal
  structures: Array Name
  ruleDepth : Nat := 0

/-- The `definitions` to be sent to Canonical,
    and the number of them which have types. -/
structure State where
  definitions: AssocList String Definition := {}
  numTypes: Nat := 0

abbrev ToCanonicalM := ReaderT Context $ StateRefT State MonoM

def modifyDefinition (key : String) (f : Definition → Definition) : ToCanonicalM Unit :=
  modify fun state => { state with definitions := state.definitions.insert key (f (state.definitions.find? key).get!) }

def setType (key : String) (type : LOption Canonical.Expr) : ToCanonicalM Unit :=
  modifyDefinition key ({ · with type })

def addEquations (key : String) (equations : Array Rule) : ToCanonicalM Unit :=
  modifyDefinition key fun defn => { defn with equations := defn.equations ++ equations }

def MAX_TYPES := 100

/-- Monad for maintaining visited in DFS. -/
abbrev WithVisited := StateT (HashSet String) Id

private partial def cyclicHelper (g : AssocList String Definition) (u : String)
    (stack : HashSet String) : WithVisited Bool := do
  if stack.contains u then
    pure true
  else if (← get).contains u then
    pure false
  else
    modify (·.insert u)
    (g.find? u).get!.neighbors.toList.anyM (λ v => cyclicHelper g v (stack.insert u))

/-- Determines whether the `neigbors` adjacency arrays in `g` are cyclic. -/
def cyclic (g : AssocList String Definition) : Bool :=
  (g.toList.anyM (λ (⟨u, _⟩ : String × Definition) => cyclicHelper g u {})).run' {}

/-- Adds an edge to `g` corresponding to the lexicographic path ordering. -/
partial def withConstraint (lhs rhs : Spine) (g : AssocList String Definition) : Option (AssocList String Definition) :=
  (g.find? lhs.head).bind fun defn =>
    if !g.contains rhs.head then
      g
    else if lhs.head == rhs.head then
      (lhs.args.zip rhs.args).firstM fun ⟨l, r⟩ => withConstraint l.spine r.spine g
    else
      let g' := g.insert lhs.head { defn with neighbors := defn.neighbors.insert rhs.head }
      rhs.args.foldlM (fun currG r => withConstraint lhs r.spine currG) g'

/-- Adds termination constraints for `rules` in the form of edges in `g`. -/
def addConstraints (rules : Array Rule) : ToCanonicalM Bool := do
  let g := (← get).definitions
  if let some g := rules.foldlM (fun g rule => withConstraint rule.lhs rule.rhs g) g then
    if !cyclic g then do
      modify fun state => { state with definitions := g }
      return true
  return false

/-- Convert `proj`, `lit`, and `forallE` into applications of a head symbol. -/
def elimSpecial (e : Lean.Expr) : MetaM Lean.Expr := do
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
      let .some info := getStructureInfo? (← getEnv) type
        | throwError ".proj of non-structure {type} currently not supported."
      return mkAppN (← withTransparency .all do (mkProjection struct info.fieldNames[idx]!)) args
    | _ => return e

/-- Defines the `<synthInstance>` symbol with type `<instImplicit>`. -/
def defineInstance (inhabited : Bool := true) : ToCanonicalM Canonical.Expr := do
  let type : Canonical.Expr := { spine := { head := "<instImplicit>" } }
  modify fun s => { s with definitions := s.definitions |>
      (·.insert "<instImplicit>" { arity := {}, type := .none }) |>
      (·.insert "<synthInstance>" { arity := {}, type := .some type }) |>
      (·.insert "<instUninhabited>" { arity := {}, type := .none }) }
  return if inhabited then type else { spine := { head := "<instUninhabited>" } }

def monomorphizePremise (name : Name) : ToCanonicalM (Bool × Array (Lean.Expr × Lean.Expr × Name)) := do
  let info ← getConstInfo name
  if (← read).config.monomorphize then
    if (← getAllBinderInfos info.type).contains .instImplicit then
      let mut result := #[]
      for ⟨expr, idx⟩ in (← monomorphizeConst name).zipIdx do
        let type ← inferType expr
        if !(← getAllBinderInfos type).contains .instImplicit then
          let monoName := Name.mkSimple ((name.num idx).toStringWithSep "_" true)
          let mvar := (← mkFreshExprMVar type .syntheticOpaque monoName).mvarId!
          mvar.assign expr
          let (mvarName, mvarType) ← toHead (.mvar mvar)
          result := result.push (expr, mvarType, mvarName)
      return (true, result)
  return (false, #[(← mkConstWithFreshMVarLevels name, info.type, name)])

def destructPremise (const : Name) (expr type : Lean.Expr) (name : Name) (simp : Bool) : ToCanonicalM (Bool × Array (Lean.Expr × Lean.Expr × Name)) := do
  if !simp && (← read).config.destruct then
    let structures := (← read).structures
    let structures := if let .some struct := ← Destruct.getStruct const then structures.erase struct else structures
    let bij ← (Destruct.destructMain type name).run (← Destruct.Context.populate structures)
    let (metas, _, _) ← lambdaMetaTelescope' bij.pack bij.unpack.size .syntheticOpaque
    let mut result := #[]
    for (destruct, m) in bij.unpack.zip metas do
      let expr := destruct.bindingBody!.instantiate1 expr
      -- m.mvarId!.assign expr
      modifyThe MonoState fun s => { s with
        mono := s.mono.insert (.sort .zero) (⟨m.mvarId!, ⟨expr, []⟩⟩ :: ((s.mono.get? (.sort .zero)).getD []))
      }
      let (mvarName, mvarType) ← toHead m
      result := result.push (expr, mvarType, mvarName)
    return (true, result)
  return (false, #[(expr, type, name)])
