import Canonical.ToCanonical
import Canonical.FromCanonical
import Canonical.Refine
import Canonical.Destruct
import Canonical.Preprocess

namespace Canonical

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
@[never_extract, extern "canonical"] opaque canonical : @& Typ → UInt64 → USize → IO CanonicalResult

/-- Terminate all invocations of `canonical` that are currently running. -/
@[never_extract, extern "cancel"] opaque cancel : IO Unit

/-- Start a server with the refinement UI on the given type. -/
@[never_extract, extern "refine"] opaque refine : @& Typ → IO Unit

/-- A version of `Core.checkInterrupted` that does not crash. -/
def interrupted : CoreM Bool := do
  if ← IO.checkCanceled then return true
  if let some tk := (← read).cancelTk? then return ← tk.isSet
  else return false

syntax premises := " [" withoutPosition(term,*,?) "]"

/-- Get the premises for inclusion, and structures to be unfolded, from the user-supplied list and the premise selector. -/
def getPremises (goal : MVarId) (premises_syntax : Option (TSyntax `Canonical.premises)) (config : CanonicalConfig) : MetaM (Array Name × Array Name) := do
  let mut premises ← if let some premises := premises_syntax then
    match premises with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]

  if config.suggestions then
    let found ← select goal
    let found := found.insertionSort (fun a b => a.score > b.score)
    let found := found.map (fun x => x.name)
    let found := found.take 3
    premises := premises ++ found

  let mut structs := #[]
  if config.destruct then
    let env ← getEnv
    structs := premises.filter fun name => isStructure env name
    premises := premises.filter fun name => !isStructure env name

  if config.pi then
    premises := premises.push ``Pi

  return (premises, structs)

/-- Run Canonical asynchronously, so that we can check for cancellation. -/
def runCanonical (typ : Typ) (timeout : UInt64) (config : CanonicalConfig) : MetaM CanonicalResult := do
  checkInterrupted
  let task ← IO.asTask (prio := .dedicated) (canonical typ timeout config.count)
  while !(← IO.hasFinished task) do
    if ← interrupted then
      cancel
      checkInterrupted
    IO.sleep 10
  IO.ofExcept task.get

/-- Perform `fromCanonical` and `reconstruct` on the terms in `result`. -/
def postprocess (result : CanonicalResult) (goal : MVarId) (config : CanonicalConfig) (reconstruct : Expr → MetaM Expr) : MetaM (Array Expr) := do
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

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => do
  let config ← canonicalConfig config
  let goal ← getMainGoal
  let (premises, structs) ← getPremises goal premises_syntax config

  let (goal', reconstruct) ← preprocess goal config structs

  let typ ← withArityUnfold config.monomorphize do goal'.withContext do
    toCanonical (← goal'.getType) premises (structs.push ``Pi) config

  if config.debug then
    Elab.admitGoal goal
    let _ ← save_to_file typ "debug.json"
    dbg_trace typ
    return

  -- Refinement UI
  if config.refine then
    let _ ← refine typ
    let fileMap ← getFileMap
    let strRange := (← getRef).getRange?.getD (panic! "No range found!")
    let range := fileMap.utf8RangeToLspRange strRange
    let width := TryThis.getInputWidth (← getOptions)
    let (indent, column) := TryThis.getIndentAndColumn fileMap strRange
    let x ← Server.WithRpcRef.mk ({
      goal := ← goal'.getType,
      lctx := ((← getMCtx).getDecl goal').lctx,
      mctx := ← getMCtx,
      mainGoal := goal,
      config,reconstruct, width, indent, column
    } : Canonical.RpcData)
    Elab.admitGoal goal
    Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef) (props := do
      let rpcData ← Server.RpcEncodable.rpcEncode x
      return Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)])
    return

  let timeout := if let some timeout := timeout_syntax then UInt64.ofNat timeout.getNat else 5
  let result ← runCanonical typ timeout config
  let proofs ← postprocess result goal' config reconstruct
  present proofs goal premises_syntax timeout_syntax
