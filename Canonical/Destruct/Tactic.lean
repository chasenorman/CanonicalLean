module

public import Lean.Elab.Tactic.Basic
public meta import Canonical.Destruct.Basic

open Lean Elab Tactic

namespace Destruct

syntax (name := destruct) "destruct " ("[" ident,* "]")? : tactic

/-- Eliminates structure types by unpacking them.  -/
@[tactic destruct] public meta def evalDestruct : Tactic
| `(tactic| destruct [$ids:ident,*]) => do
  let names ← ids.getElems.mapM resolveGlobalConstNoOverload
  liftMetaTactic fun x => do
    let destruct ← destructTactic x (STRUCTURES ++ names)
    pure (destruct.map (·.2)).toList
| `(tactic| destruct) => do
  liftMetaTactic fun x => do
    let destruct ← destructTactic x STRUCTURES
    pure (destruct.map (·.2)).toList
| _ => throwUnsupportedSyntax
