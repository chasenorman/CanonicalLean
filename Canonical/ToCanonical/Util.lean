module

import Lean
public import Lean.Expr
public import Lean.Elab.Term.TermElabM
public import Lean.Elab.Tactic.Basic
public import Lean.Data.AssocList
public import Canonical.Basic
public import Canonical.Util
public import Canonical.Monomorphize.Basic
import Canonical.Destruct.Basic
import Canonical.Symbols

open Lean hiding Term
open Meta Expr Std Monomorphize

namespace Canonical

public section

structure CanonicalConfig where
  /-- Canonical produces `count` proofs. -/
  count: USize := 1
  /-- Provide `(A → B) : Sort` as an axiom to Canonical. -/
  pi: Bool := false
  /-- Print the inhabitation problem sent to Canonical. -/
  debug: Bool := false
  /-- Open the refinement UI. -/
  refine: Bool := false
  /-- Allow Canonical to use `simp`. -/
  simp: Bool := true
  /-- Resolve typeclass instances in a preprocessing stage. -/
  monomorphize: Bool := true
  /-- Unpacks structure types in a preprocessing stage.  -/
  destruct: Bool := true
  /-- Add premises from the current premise selector. -/
  suggestions: Bool := false

declare_config_elab canonicalConfig CanonicalConfig

/-- Definition of a symbol during translation,
    to be converted into `(Let × Option Typ)` -/
structure Definition where
  /-- `.undef` corresponds to a definition without translated type,
      but may acquire one as the translation progresses. -/
  type: LOption Typ
  arity: Arity
  rules: Array Rule := #[]
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
  config: CanonicalConfig
  polarity: Polarity := .goal
  structures: Array Name
  ruleDepth : Nat := 0

/-- The `definitions` to be sent to Canonical,
    and the number of them which have types. -/
structure State where
  definitions: AssocList String Definition := {}
  numTypes: Nat := 0

abbrev ToCanonicalM := ReaderT Context $ StateRefT State MonoM

def toVar (e : Expr) : MetaM Var := do pure { name := ← toNameString e }

def setType (key : String) (typ : LOption Typ) : ToCanonicalM Unit := do
  modify fun state => { state with definitions := state.definitions.insert key {
    (state.definitions.find? key).get! with type := typ } }

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
      let .some info := getStructureInfo? (← getEnv) type
        | throwError ".proj of non-structure {type} currently not supported."
      return mkAppN (← withTransparency .all do (mkProjection struct info.fieldNames[idx]!)) args
    | _ => return e

/-- Defines the `<synthInstance>` symbol with type `<instImplicit>`. -/
def defineInstance (inhabited : Bool := true) : ToCanonicalM Typ := do
  let typ : Typ := { spine := { head := "<instImplicit>" } }
  modify (fun s => { s with definitions := (
    (s.definitions.insert "<instImplicit>" { arity := {}, type := .none }).insert "<synthInstance>" { arity := {}, type := .some typ } ).insert "<instUninhabited>" { arity := {}, type := .none } })
  return if inhabited then typ else { spine := { head := "<instUninhabited>" } }

def monomorphizePremise (name : Name) : ToCanonicalM (Bool × Array (Expr × Expr × Name)) := do
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

def destructPremise (const : Name) (premise : Expr × Expr × Name) (simp : Bool) : ToCanonicalM (Bool × Array (Expr × Expr × Name)) := do
  if !simp && (← read).config.destruct then
    let structures := NameSet.ofArray (Destruct.STRUCTURES ++ (← read).structures)
    let structures := if let .some struct := ← Destruct.getStruct const then structures.erase struct else structures
    if let (some (construct, destruct), _) ← (Destruct.separatePi premise.2.1 premise.2.2 .default).run structures then
      let (metas, _, _) ← lambdaMetaTelescope' construct destruct.size .syntheticOpaque
      let mut result := #[]
      for (destruct, m) in destruct.zip metas do
        let expr := destruct.bindingBody!.instantiate1 premise.1
        -- m.mvarId!.assign expr
        modifyThe MonoState fun s => { s with
          mono := s.mono.insert (.sort .zero) (⟨m.mvarId!, ⟨expr, []⟩⟩ :: ((s.mono.get? (.sort .zero)).getD []))
        }
        let (mvarName, mvarType) ← toHead m
        result := result.push (expr, mvarType, mvarName)
      return (true, result)
  return (false, #[premise])
