module

public meta import Canonical.Monomorphize.Basic
public import Lean.Elab.Tactic.Basic
open Lean Elab Tactic

namespace Monomorphize

syntax (name := monomorphize) "monomorphize " Parser.Tactic.optConfig ("[" ident,* "]")? : tactic

@[tactic monomorphize] public meta def evalMonomorphize : Tactic
| `(tactic| monomorphize $config [$ids:ident,*]) => do
  let config ← monoConfig config
  liftMetaTactic1 fun goal =>
    goal.withContext do
      (monomorphizeTactic goal ids.getElems config).run' { globalFVars := .ofArray (← getLCtx).getFVarIds }
| `(tactic| monomorphize $config) => do
  let config ← monoConfig config
  liftMetaTactic1 fun goal =>
    goal.withContext do
      (monomorphizeTactic goal #[] config).run' { globalFVars := .ofArray (← getLCtx).getFVarIds }
| _ => throwUnsupportedSyntax
