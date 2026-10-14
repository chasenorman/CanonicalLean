import Canonical.Main
import Canonical.ToCanonical.Main

open Lean Meta Canonical

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let ctx : Core.Context := { fileName := "<check>", fileMap := default }
  let state : Core.State := { env }
  let config : Canonical.Config := { count := 1, simp := false, destruct := false, monomorphize := false }
  let act : MetaM Nat := do
    let mvar ← mkFreshExprMVar (mkConst ``Nat)
    let decl ← withArityUnfold false do
      toCanonical "proof" (← mvar.mvarId!.getType) #[] #[] config
    return (← runCanonical decl 1 config).terms.size
  match ← ((act.run {} {} >>= fun (n, _) => pure n).run' ctx state).toBaseIO with
  | .ok n =>
    IO.println s!"terms: {n}"
    return 0
  | .error _ =>
    IO.eprintln "canonical failed"
    return 1
