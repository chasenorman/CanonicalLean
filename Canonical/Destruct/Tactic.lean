module

public meta import Canonical.Destruct.Basic
public meta import Canonical.Destruct.Unary
public import Lean.Elab.Tactic.Basic

open Lean Elab Tactic

namespace Destruct

syntax (name := destruct) "destruct " ("[" ident,* "]")? : tactic
syntax (name := unary) "unary " ("[" ident,* "]")? : tactic

/-- Eliminates structure types by unpacking them.  -/
@[tactic destruct] public meta def evalDestruct : Tactic
| `(tactic| destruct [$ids:ident,*]) => do
  let names ← ids.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic fun x => do
    let destruct ← destructTactic x (STRUCTURES ++ names)
    if !destruct.1 then
      logWarning "destruct made no progress."
    pure (destruct.2.map (·.2))
| `(tactic| destruct) => do
  liftMetaTactic fun x => do
    let destruct ← destructTactic x STRUCTURES
    if !destruct.1 then
      logWarning "destruct made no progress."
    pure (destruct.2.map (·.2))
| _ => throwUnsupportedSyntax

@[tactic unary] public meta def evalUnaryDestruct : Tactic
| `(tactic| unary [$ids:ident,*]) => do
  let names ← ids.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic fun x => do
    let destruct ← Unary.destructTactic x (Unary.STRUCTURES ++ names)
    pure (destruct.map (·.2)).toList
| `(tactic| unary) => do
  liftMetaTactic fun x => do
    let destruct ← Unary.destructTactic x Unary.STRUCTURES
    pure (destruct.map (·.2)).toList
| _ => throwUnsupportedSyntax

-- example (f : Nat × Nat → Nat) (g : Nat → Nat × Nat) (y : Nat × Nat × Nat) : Nat := by
--   unary
