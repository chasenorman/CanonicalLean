module

public meta import Canonical.ToCanonical.Main
public meta import Canonical.Main
public meta import Canonical.Refine
import Canonical.Symbols

open Lean Parser Tactic Meta Elab Tactic Core LibrarySuggestions Server

namespace Canonical

public meta section

syntax premises := " [" withoutPosition(term,*,?) "]"

declare_config_elab canonicalConfig Config

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => do
  let config ← canonicalConfig config
  let goal ← getMainGoal

  let consts ← if let some consts := premises_syntax then
    match consts with
    | `(premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
    | _ => Elab.throwUnsupportedSyntax
    else pure #[]
  let (premises, structs) ← getPremises goal consts config

  let (processedGoal, reconstruct) ← withArityUnfold config.monomorphize do
    preprocess goal config structs

  let typ ← withArityUnfold config.monomorphize do processedGoal.withContext do
    toCanonical (← processedGoal.getType) premises (structs.push ``Pi) config

  if config.debug then
    Elab.admitGoal goal
    save_typ typ "debug.json"
    dbg_trace typ
    return

  -- Refinement UI
  if config.refine then
    let _ ← refine typ
    let (width, indent, column, range) ← widthIndentColumnRange
    let x : WithRpcRef RpcData ← WithRpcRef.mk {
      mctx := ← getMCtx, mainGoal := goal,
      config, reconstruct, width, indent, column, processedGoal
    }
    Elab.admitGoal goal
    Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef) (props := do
      let rpcData ← RpcEncodable.rpcEncode x
      return Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)])
    return

  let timeout := if let some timeout := timeout_syntax then UInt64.ofNat timeout.getNat else 5
  let name := ((← Lean.Elab.Term.getDeclName?).map toString).getD "proof"
  let result ← runCanonical typ name timeout config
  let proofs ← postprocess result processedGoal config reconstruct
  present proofs goal premises_syntax timeout_syntax
