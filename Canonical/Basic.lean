import Lean

open Lean.Meta Lean.Elab

namespace Canonical

/-- A variable binding. -/
structure Var where
  name: String
deriving Inhabited, Repr

mutual
  /-- A let binding is a variable binding with reduction rules. -/
  structure Let extends Var where
    rules: Array Rule := #[]
  deriving Inhabited, Repr

  /-- A spine is an n-ary, η-long application of a head symbol. -/
  structure Spine where
    head: String
    args: Array Term := #[]

    /-- For proof reconstruction, the reduction rules applied
        to the type of this spine. -/
    premiseRules : Array String := #[]
  deriving Inhabited, Repr

  /-- A term is an n-ary, β-normal, η-long λ expression:
      `λ params lets . spine` -/
  structure Term where
    params: Array Var := #[]
    lets: Array Let := #[]
    spine: Spine

    /-- For proof reconstruction, the reduction rules applied
        to the type of the metavariable hole. -/
    goalRules : Array String := #[]
  deriving Inhabited, Repr

  /-- A reduction rule `lhs ↦ rhs`. The `attribution` will be added
      to the `premiseRules` or `goalRules` arrays where used.
      Canonical will not return a term that reduces according to
      a rule that `isRedex`. -/
  structure Rule where
    lhs: Spine
    rhs: Spine
    attribution: Array String := #[]
    isRedex: Bool := true
  deriving Inhabited, Repr
end

/-- A type is an n-ary Π-type: `Π params lets . toTerm` -/
structure Typ extends Term where
  paramTypes: Array (Option Typ) := #[]
  letTypes: Array (Option Typ) := #[]
deriving Inhabited, Repr

@[never_extract, extern "spine_to_string"] opaque spineToString: @& Spine → String
instance : ToString Spine where toString := spineToString

@[never_extract, extern "term_to_string"] opaque termToString: @& Term → String
instance : ToString Term where toString := termToString

@[never_extract, extern "typ_to_string"] opaque typToString: @& Typ → String
instance : ToString Typ where toString := typToString

instance : ToString Rule where
  toString r := s!"{r.lhs} ↦ {r.rhs}"

/-- Saves a JSON representation of the type to the given file. -/
@[never_extract, extern "save_to_file"] opaque save_to_file : @& Typ → String → IO Unit
