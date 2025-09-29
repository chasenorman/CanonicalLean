import Canonical.Destruct
import Canonical.TranslationUtil
import Lean

open Lean

namespace Canonical

def preprocessOfNat (e : Expr) : Expr :=
  e.replace fun e =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.constName == ``One.one then
      if let #[α, inst] := args then
        let u := fn.constLevels!
        let ofNatInst := mkApp2 (mkConst ``One.toOfNat1 u) α inst
        let rhs := mkApp3 (mkConst ``OfNat.ofNat u) α (mkRawNatLit 1) ofNatInst
        some rhs
      else none
    else if fn.constName == ``Zero.zero then
      if let #[α, inst] := args then
        let u := fn.constLevels!
        let ofNatInst := mkApp2 (mkConst ``Zero.toOfNat0 u) α inst
        let rhs := mkApp3 (mkConst ``OfNat.ofNat u) α (mkRawNatLit 0) ofNatInst
        some rhs
      else none
    else none

def preprocess (goal : MVarId) (config : CanonicalConfig) (structs : Array Name) : MetaM (MVarId × (Expr → MetaM Expr)) := do
  if config.destruct then
    if let some (goal, transform) ← Destruct.destructCanonical goal structs then
      return (goal, fun x => do pure (preprocessOfNat (← transform x)))
  return (goal, fun x => pure (preprocessOfNat x))

end Canonical
