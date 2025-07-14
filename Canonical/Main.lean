import Canonical.ToCanonical

namespace Canonical

open Lean Parser Tactic Meta Elab Tactic
syntax premises := " [" withoutPosition(term,*,?) "]"

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout:(num)? config:optConfig premises:(premises)? : tactic => do
  let premises ← if let some premises := premises then
    match premises with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]

  withArityUnfold do withMainContext do
    let goal ← getMainTarget
    dbg_trace (← toCanonical goal premises)
