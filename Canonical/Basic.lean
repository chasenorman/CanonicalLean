import Lean

open Lean.Meta Lean.Elab

namespace Canonical

structure Var where
  name: String
deriving Inhabited, Repr

mutual
  structure Let extends Var where
    rules: Array Rule := #[]
  deriving Inhabited, Repr

  structure Spine where
    head: String
    args: Array Term := #[]

    premiseRules : Array String := #[]
  deriving Inhabited, Repr

  structure Term where
    params: Array Var := #[]
    lets: Array Let := #[]
    spine: Spine

    goalRules : Array String := #[]
  deriving Inhabited, Repr

  structure Rule where
    lhs: Spine
    rhs: Spine
    attribution: Array String := #[]
    isRedex: Bool := true
  deriving Inhabited, Repr
end

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
