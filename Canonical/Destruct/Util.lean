module

import Lean.Structure
import Lean.ProjFns
public import Lean.Meta.Basic

open Lean Meta

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
  /-- Allows the destruct tactic to determine whether the Bijection has made
  simplifications (not including beta reduction) to the type -/
  madeProgress : Bool := false
deriving Inhabited

def apply (fn : Expr) (arg : Expr) : Expr :=
  (Expr.app fn arg).headBeta

def applyN (fn : Expr) (args : Array Expr) : Expr :=
  (mkAppN fn args).headBeta

def lambdaBinderNames (lam : Expr) (n : Nat) (result : Array Name := #[]) : Array Name :=
  match lam, n with
  | .lam name _ body _, .succ n => lambdaBinderNames body n (result.push name)
  | _, _ => result

partial def packTelescope {α} (info : List (Bijection × Expr)) (k : Array Expr → Array Expr → MetaM α)
  (context : Array Expr := #[]) (vars : Array Expr := #[]) (packs : Array Expr := #[]) : MetaM α := do
  match info with
  | (bij, x)::info =>
    let pack := bij.pack.replaceFVars context packs
    lambdaBoundedTelescope pack bij.unpack.size fun newVars packed => do
      packTelescope info k (context.push x) (vars ++ newVars) (packs.push packed)
  | [] => k vars packs

partial def lambdaBoundedTelescopeDestruct {α} (lam : Expr) (n : Nat) (vars : Array Expr) (k : Array Expr → Expr → MetaM α) (fs : Array Expr := #[]) : MetaM α :=
  match lam, n with
  | .lam name type body _, .succ n => do
    withLocalDeclD name (← mkForallFVars vars type) fun f => do
      lambdaBoundedTelescopeDestruct (body.instantiate1 (mkAppN f vars)) n vars k (fs.push f)
  | _, _ => k fs lam

def prefixName (binderName : Name) (userName : Name) : Name :=
  if binderName.isInternal then userName
  else (binderName.toString ++ "_" ++ userName.toString).toName

def getStruct (name : Name) : MetaM (Option Name) := do
  let env ← getEnv
  if let some (.ctorInfo info) := env.find? name then
    if isStructure env info.name then
      return info.name
  return env.getProjectionStructureName? name
