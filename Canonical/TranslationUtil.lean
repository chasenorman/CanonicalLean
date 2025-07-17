import Canonical.Basic
import Canonical.Util
import Canonical.Monomorphize
import Canonical.Reduction
import Canonical.Simp
import Lean

open Lean hiding Term
open Meta Expr Std Monomorphize

namespace Canonical

structure CanonicalConfig where
  /-- Canonical produces `count` proofs. -/
  count: USize := 1
  /-- Provides `(A → B) : Sort` as an axiom to Canonical. -/
  pi: Bool := false
  debug: Bool := false
  /-- Opens the refinement UI. -/
  refine: Bool := false
  simp: Bool := true
  monomorphize: Bool := true
  premises: Bool := false

declare_config_elab canonicalConfig CanonicalConfig

structure Definition where
  type: LOption Typ
  arity: Arity
  rules: Array Rule := #[]
  neighbors: HashSet String := {}
deriving Inhabited

inductive Polarity where
| premise
| goal

def flip : Polarity → Polarity
| .premise => .goal
| .goal => .premise

structure Context where
  arities: HashMap FVarId Arity
  noTypes: Bool := false
  config: CanonicalConfig
  polarity: Polarity := .goal

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

def defineInstance : ToCanonicalM Typ := do
  let typ : Typ := { spine := { head := "<instImplicit>" } }
  modify (fun s => { s with definitions := (
    s.definitions.insert "<instImplicit>" { arity := {}, type := .none }).insert "<synthInstance>" { arity := {}, type := .some typ } })
  return typ
