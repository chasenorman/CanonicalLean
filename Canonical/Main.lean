module

public import Lean
public import Canonical.Util
public import Canonical.Basic
import Canonical.Symbols
import Canonical.Destruct.Basic
import Canonical.FromCanonical

namespace Canonical

public section

open Lean Parser Tactic Meta Elab Tactic Core LibrarySuggestions

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
@[never_extract, extern "canonical"] opaque canonical : @& Typ → String → UInt64 → USize → IO CanonicalResult

/-- Terminate all invocations of `canonical` that are currently running. -/
@[never_extract, extern "cancel"] opaque cancel : IO Unit

/-- Start a server with the refinement UI on the given type. -/
@[never_extract, extern "refine"] opaque refine : @& Typ → IO Unit

/-- Get the premises for inclusion, and structures to be unfolded, from the user-supplied list and the premise selector. -/
def getPremises (goal : MVarId) (consts : Array Name) (config : Config) : MetaM (Array Name × Array Name) := do
  let mut premises := consts

  if config.suggestions then
    let found ← select goal
    let found := found.insertionSort (fun a b => a.score > b.score)
    let found := found.map (fun x => x.name)
    let found := found.take 3
    premises := premises ++ found

  let mut structs := #[]
  if config.destruct then
    let env ← getEnv
    structs ← premises.filterMapM Destruct.getStruct
    structs := structs ++ (premises.filter (isStructure env))
    premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone

  if config.pi then
    premises := premises.push ``Pi

  return (premises, structs)

def preprocess (goal : MVarId) (config : Config) (structs : Array Name) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  if config.destruct then
    if let some (goal, reconstruct) ← Destruct.destructCanonical goal structs then
      return (goal, reconstruct)
  return (goal, pure)

/-- Run Canonical asynchronously, so that we can check for cancellation. -/
def runCanonical (typ : Typ) (name : String) (timeout : UInt64) (config : Config) : MetaM CanonicalResult := do
  checkInterrupted
  let task ← IO.asTask (prio := .dedicated) (canonical typ name timeout config.count.toUSize)
  while !(← IO.hasFinished task) do
    if ← interrupted then
      cancel
      checkInterrupted
    IO.sleep 10
  IO.ofExcept task.get

/-- Perform `fromCanonical` and `reconstruct` on the terms in `result`. -/
def postprocess (result : CanonicalResult) (goal : MVarId) (config : Config) (reconstruct : Expr → MetaM Expr) : MetaM (Array Expr) := do
  withArityUnfold config.monomorphize do goal.withContext do
    let proofs ← result.terms.mapM fun term => do fromCanonical term (← goal.getType)
    let proofs ← proofs.mapM reconstruct
    return proofs

/-- If no proof was found, show a relevant error. Otherwise, suggest the proofs. -/
def present (proofs : Array Expr) (goal : MVarId)
  (premises_syntax : Option (TSyntax `Canonical.premises)) (timeout_syntax : Option (TSyntax `num)) : TacticM Unit := do
  if proofs.isEmpty then
    match premises_syntax with
    | some _ => match timeout_syntax with
      | some _ => throwError "No proof found."
      | none => throwError "No proof found. Change timeout to `n` with `canonical n`"
    | none => throwError "No proof found. Supply constant symbols with `canonical [name, ...]`"

  goal.withContext do withOptions applyOptions do
    Elab.admitGoal goal
    if h : proofs.size = 1 then
      TryThis.addExactSuggestion (← getRef) proofs[0]
    else
      TryThis.addExactSuggestions (← getRef) proofs
