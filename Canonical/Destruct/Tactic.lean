import Canonical.Destruct.Basic
import Lean

open Lean Elab Tactic

namespace Destruct

syntax (name := destruct) "destruct " ("[" ident,* "]")? : tactic

/-- Eliminates structure types by unpacking them.  -/
@[tactic destruct] def evalDestruct : Tactic
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
