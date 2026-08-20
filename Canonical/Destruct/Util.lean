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

  -- TODO: Find a better place to put this
  -- Specifically for destructTactic to determine the unpacked arities of
  -- functions
  arities : Option (List Nat)
  deriving Inhabited

def Bijection.p (b : Bijection) : String :=
  let arities := b.arities
  let pack := b.pack
  let unpack := b.unpack.map fun e => s!"{e}"
  let unpack' := "\n  ".intercalate unpack.toList
  s!"\{\n arities := {arities},\n pack := {pack},\n unpack := [\n  {unpack'}\n ]\n}"

def Bijection.pp (b : Bijection) : MetaM String := do
  let arities := b.arities
  let pack ← ppExpr b.pack
  let unpack ← b.unpack.mapM fun e => do return toString (← ppExpr e)
  let unpack' := "\n  ".intercalate unpack.toList
  return s!"\{\n arities := {arities},\n pack := {pack},\n unpack := [\n  {unpack'}\n ]\n}"

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

partial def packTelescope (bijs : Array Bijection) (fvars : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α := do
  let rec recurse (i : Nat) (varBlocks : Array (Array Expr)) (packedBlocks : Array Expr) (k : Array (Array Expr) → Array Expr → MetaM α) : MetaM α := do
    if i == bijs.size then return ← k varBlocks packedBlocks
    let b := bijs[i]!
    let pack := b.pack.replaceFVars (fvars.take i) packedBlocks
    lambdaBoundedTelescope pack b.unpack.size fun vars packed => do
      recurse (i + 1) (varBlocks.push vars) (packedBlocks.push packed) k
  recurse 0 #[] #[] k
