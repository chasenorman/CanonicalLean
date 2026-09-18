module

import Lean
public import Lean.Expr
public import Lean.Meta.Basic

open Lean Core Meta

namespace Destruct

public section

/-- A mapping between an expression `e` and its constituent expressions `e₁`,
    ..., `eₙ`.

    - The field `pack` is of the form `λ x₁ … xₙ ↦ ⟨…⟩`
    - The field `unpack` is of the form `#[λ x ↦ (…).1, …, λ x ↦ (…).n]`
-/
structure Bijection where
  pack : Expr
  unpack : Array Expr
  /-- For destructTactic to determine the unpacked arities of functions -/
  arities : List Nat := []
deriving Inhabited

def apply (fn : Expr) (arg : Expr) : Expr :=
  match fn with
  | Expr.lam _ _ body _ => body.instantiate1 arg
  | _ => panic! s!"Destruct.apply expected a lambda, got {fn}"

def applyN (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (fun app arg => apply app arg) fn

def lambdaBinders (lam : Expr) (n : Nat) : List (Name × Expr) :=
  if n == 0 then [] else
  match lam with
  | Expr.lam name type body _ => (name, type)::lambdaBinders body (n-1)
  | _ => panic! s!"Destruct.lambdaBinders expected a lambda, got {lam}"

partial def packTelescope {α} (bijs : Array Bijection) (fvars : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α)
  (i : Nat := 0) (varBlocks : Array (Array Expr) := #[]) (packedBlocks : Array Expr := #[]) : MetaM α := do
  if h : i < bijs.size then
    let pack := bijs[i].pack.replaceFVars (fvars.take i) packedBlocks
    lambdaBoundedTelescope pack bijs[i].unpack.size fun vars packed => do
      packTelescope bijs fvars k (i + 1) (varBlocks.push vars) (packedBlocks.push packed)
  else k varBlocks packedBlocks

def getStruct (name : Name) : MetaM (Option Name) := do
  let env ← getEnv
  if let some (.ctorInfo info) := env.find? name then
    if isStructure env info.name then
      return info.name
  return env.getProjectionStructureName? name
