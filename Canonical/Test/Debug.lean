import Lean
import Canonical.Test.Common

open Lean Meta SubExpr

def run (const : Name) (pos : Pos) (premises : NameSet) : MetaM Unit := do
  let value := (← getConstInfo const).value! (allowOpaque := true)
  viewSubexpr (fun _ e => do
    IO.println s!"Goal: {← ppExpr (← inferType e)}"
    let proofs ← canonicalSimple (← inferType e) premises (verbose := true) (witness := some e)
    if h : proofs.size > 0 then
      IO.println s!"Proof: {← ppExpr proofs[0]}"
    else
      IO.println "No proof found."
  ) pos value

/-- `lake exe debug <const> <pos> [premise...]`, as printed by `lake exe robustness`. -/
unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | const :: pos :: premises =>
    let pos ← IO.ofExcept (Pos.fromString? pos)
    let const := parseName const
    -- Same environment as `lake exe robustness`.
    runMetaWith #[`Std] <| run const pos (NameSet.ofList (premises.map parseName))
    return 0
  | _ =>
    IO.eprintln "usage: lake exe debug <const> <pos> [premise...]"
    return 1
