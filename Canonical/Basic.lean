module

import Lean

open Lean Meta Elab

namespace Canonical

public section

mutual
  /-- A let binding is a variable binding with reduction rules. -/
  structure Decl where
    name: String
    type: Option Expr := none
    equations: Array Rule := #[]
  deriving Inhabited, Repr

  /-- A spine is an n-ary, η-long application of a head symbol. -/
  structure Spine where
    head: String
    args: Array Expr := #[]

    /-- For proof reconstruction, the reduction rules applied
        to the type of this spine. -/
    premiseRules : Array String := #[]
  deriving Inhabited, Repr

  /-- A term is an n-ary, β-normal, η-long λ expression:
      `λ params lets . spine` -/
  structure Expr where
    params: Array Decl := #[]
    lets: Array Decl := #[]
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

@[never_extract, extern "spine_to_string"] opaque spineToString: @& Spine → String
instance : ToString Spine where toString := spineToString

-- @[never_extract, extern "term_to_string"] opaque termToString: @& Term → String
-- instance : ToString Term where toString := termToString

@[never_extract, extern "typ_to_string"] opaque typToString: @& Expr → String
instance : ToString Expr where toString := typToString

@[never_extract, extern "rule_to_string"] opaque ruleToString: @& Rule → String
instance : ToString Rule where toString := ruleToString

/-- Saves a JSON representation of the type to the given file. -/
@[never_extract, extern "save_problem"] opaque save_problem : @& Decl → String → IO Unit

structure Config where
  /-- Canonical produces `count` proofs. -/
  count: Nat := 1
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
