module

import Canonical.Symbols
public meta import Canonical.ToCanonical.Main
public meta import Canonical.Main
public meta import Canonical.Refine

open Lean Parser Tactic Meta Elab Tactic Core LibrarySuggestions

namespace Canonical

public section

syntax premises := " [" withoutPosition(term,*,?) "]"

/-- Get the premises for inclusion, and structures to be unfolded, from the user-supplied list and the premise selector. -/
meta def getPremises (goal : MVarId) (premises_syntax : Option (TSyntax `Canonical.premises)) (config : CanonicalConfig) : MetaM (Array Name × Array Name) := do
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
    structs ← premises.filterMapM Destruct.getStruct
    structs := structs ++ (premises.filter (isStructure env))
    premises ← premises.filterM fun name => do pure (← Destruct.getStruct name).isNone

  if config.pi then
    premises := premises.push ``Pi

  return (premises, structs)

/-- Canonical exhaustively searches for terms in dependent type theory. -/
elab (name := canonicalSeq) "canonical " timeout_syntax:(num)? config:optConfig premises_syntax:(premises)? : tactic => do
  let config ← canonicalConfig config
  let goal ← getMainGoal
  let (premises, structs) ← getPremises goal premises_syntax config

  let (goal', reconstruct) ← withArityUnfold config.monomorphize do preprocess goal config structs

  let typ ← withArityUnfold config.monomorphize do goal'.withContext do
    toCanonical (← goal'.getType) premises (structs.push ``Pi) config

  if config.debug then
    Elab.admitGoal goal
    save_typ typ "debug.json"
    dbg_trace typ
    return

  -- Refinement UI
  if config.refine then
    let _ ← refine typ
    let (width, indent, column, range) ← widthIndentColumnRange
    let x ← Server.WithRpcRef.mk ({
      goal := ← goal'.getType,
      lctx := ((← getMCtx).getDecl goal').lctx,
      mctx := ← getMCtx,
      mainGoal := goal,
      config, reconstruct, width, indent, column
    } : Canonical.RpcData)
    Elab.admitGoal goal
    Widget.savePanelWidgetInfo (hash refineWidget.javascript) (← getRef) (props := do
      let rpcData ← Server.RpcEncodable.rpcEncode x
      return Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)])
    return

  let timeout := if let some timeout := timeout_syntax then UInt64.ofNat timeout.getNat else 5
  let name := ((← Lean.Elab.Term.getDeclName?).map toString).getD "proof"
  let result ← runCanonical typ name timeout config
  let proofs ← postprocess result goal' config reconstruct
  present proofs goal premises_syntax timeout_syntax
