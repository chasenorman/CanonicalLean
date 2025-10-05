import Canonical.ToCanonical
import Canonical.FromCanonical
import Canonical.Refine
import Canonical.Destruct
import Canonical.Preprocess

namespace Canonical

open Lean Parser Tactic Meta Elab Tactic Core LibrarySearch PremiseSelection

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

/-- A version of `Core.checkInterrupted` that does not crash. -/
def interrupted : CoreM Bool := do
  if let some tk := (← read).cancelTk? then return ← tk.isSet
  else return false

/-- Metaprogramming interface for CanonicalLean. This function adds the LCtx as premises. -/
def canonicalLean (goal : Expr) (premises : Array Name) (structures : Array Name := #[]) (timeout : UInt64) (config : CanonicalConfig) : MetaM (Array Expr) := do
  let typ ← toCanonical goal premises (structures.push ``Pi) config
  let result ← canonical typ timeout config.count
  result.terms.mapM fun term => fromCanonical term goal

syntax premises := " [" withoutPosition(term,*,?) "]"

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => do
  let mut premises ← if let some premises := premises_syntax then
    match premises with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]

  let timeout := if let some timeout := timeout_syntax then timeout.getNat else 5

  let config ← canonicalConfig config

  if config.librarySearch then
    let (_, goal) ← (← getMainGoal).intros
    goal.withContext do
    premises := premises ++ (← librarySearchSymm libSearchFindDecls (← getMainGoal)).map (·.2.1)

  if config.premises then
    let found ← select (← getMainGoal)
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

  let (goal, reconstruct) ← preprocess (← getMainGoal) config structs

  withArityUnfold config.monomorphize do goal.withContext do
    let goal ← goal.getType

    let typ ← toCanonical goal premises (structs.push ``Pi) config

    if config.debug then
      Elab.admitGoal (← getMainGoal)
      let _ ← save_to_file typ "debug.json"
      dbg_trace typ
      return

    -- Refinement UI
    if config.refine then
      let _ ← refine typ
      let fileMap ← getFileMap
      let strRange := (← getRef).getRange?.getD (panic! "No range found!")
      let range := fileMap.utf8RangeToLspRange strRange
      let width := Lean.Meta.Tactic.TryThis.getInputWidth (← getOptions)
      let (indent, column) := Lean.Meta.Tactic.TryThis.getIndentAndColumn fileMap strRange
      let x ← Server.WithRpcRef.mk (RpcData.mk goal config (← getLCtx) (← getMCtx) (← getMainGoal) reconstruct width indent column)
      Elab.admitGoal (← getMainGoal)
      Lean.Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef)
        (props := do
          let rpcData ← Server.RpcEncodable.rpcEncode x
          pure (Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)]))
      return

    -- Run Canonical asynchronously, so that we can check for cancellation.
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
    let proofs ← proofs.mapM (fun x => reconstruct x)

    if proofs.isEmpty then
      match premises_syntax with
      | some _ => match timeout_syntax with
        | some _ => throwError "No proof found."
        | none => throwError "No proof found. Change timeout to `n` with `canonical n`"
      | none => throwError "No proof found. Supply constant symbols with `canonical [name, ...]`"

    (← getMainGoal).withContext do
      withOptions applyOptions do
        Elab.admitGoal (← getMainGoal)
        if h : proofs.size = 1 then
          Meta.Tactic.TryThis.addExactSuggestion (← getRef) proofs[0]
        else
          Meta.Tactic.TryThis.addExactSuggestions (← getRef) proofs
