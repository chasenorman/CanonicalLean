import Canonical.ToCanonical
import Canonical.FromCanonical

namespace Canonical

open Lean Parser Tactic Meta Elab Tactic Core

/-- The return type of Canonical, with the generated `terms`. -/
structure CanonicalResult where
  terms: Array Term
  attempted_resolutions: UInt32
  successful_resolutions: UInt32
  steps: UInt32
  last_level_steps: UInt32
  branching: Float32
deriving Inhabited

/-- Generate terms of a given type, with given timeout and desired count. -/
@[never_extract, extern "canonical"] opaque canonical : @& Typ → UInt64 → USize → IO CanonicalResult

/-- Start a server with the refinement UI on the given type. -/
@[never_extract, extern "refine"] opaque refine : @& Typ → IO Unit

/-- Obtains the current term from the refinement UI. -/
@[never_extract, extern "get_refinement"] opaque getRefinement : IO Tm

/-- A version of `Core.checkInterrupted` that does not crash. -/
def interrupted : CoreM Bool := do
  if let some tk := (← read).cancelTk? then return ← tk.isSet
  else return false

def applyOptions : Options → Options :=
  (pp.proofs.set · true |>
  (pp.motives.all.set · true |>
  (pp.coercions.set · false |>
  (pp.unicode.fun.set · true))))

structure CanonicalConfig where
  /-- Canonical produces `count` proofs. -/
  count: USize := 1
  /-- Provides `(A → B) : Sort` as an axiom to Canonical. -/
  pi: Bool := false
  debug: Bool := false
  /-- Opens the refinement UI. -/
  refine: Bool := false
  simp: Bool := true
  monomorphize: Bool := true

declare_config_elab canonicalConfig CanonicalConfig

syntax premises := " [" withoutPosition(term,*,?) "]"

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => do
  let premises ← if let some premises := premises_syntax then
    match premises with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]

  let timeout := if let some timeout := timeout_syntax then timeout.getNat else 5

  let config ← canonicalConfig config
  let premises := if config.pi then premises.push ``Pi else premises

  withArityUnfold do withMainContext do
    let goal ← getMainTarget
    let typ ← toCanonical goal premises

    if config.debug then
      Elab.admitGoal (← getMainGoal)
      let _ ← save_to_file typ "debug.json"
      dbg_trace typ
      return

    checkInterrupted
    let task ← IO.asTask (prio := .dedicated)
      (canonical typ (UInt64.ofNat timeout) config.count)
    while !(← IO.hasFinished task) do
      if ← interrupted then
        IO.cancel task
        checkInterrupted
      IO.sleep 10

    let result ← IO.ofExcept task.get
    let proofs ← result.terms.mapM fun term => fromCanonical term goal

    if proofs.isEmpty then
      match premises_syntax with
      | some _ => match timeout_syntax with
        | some _ => throwError "No proof found."
        | none => throwError "No proof found. Change timeout to `n` with `canonical n`"
      | none => throwError "No proof found. Supply constant symbols with `canonical [name, ...]`"

    withOptions applyOptions do
      Elab.admitGoal (← getMainGoal)
      if h : proofs.size = 1 then
        Meta.Tactic.TryThis.addExactSuggestion (← getRef) proofs[0]
      else
        Meta.Tactic.TryThis.addExactSuggestions (← getRef) proofs
