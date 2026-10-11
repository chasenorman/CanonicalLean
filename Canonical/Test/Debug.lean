import Lean
import Canonical.Test.Common

open Lean Meta SubExpr

/-- `viewSubexpr`, except that let binders enter the context with their `nondep` flag,
    matching `traverseChildren` in `lake exe robustness`. -/
partial def view (k : Expr → MetaM α) : List Nat → Expr → MetaM α
  | [], e => k e
  | c :: cs, .mdata _ e => view k (c :: cs) e
  | 0 :: cs, .app f _ => view k cs f
  | 1 :: cs, .app _ a => view k cs a
  | 0 :: cs, .lam _ t _ _ | 0 :: cs, .forallE _ t _ _ | 0 :: cs, .letE _ t _ _ _ => view k cs t
  | 1 :: cs, .lam n t b bi | 1 :: cs, .forallE n t b bi =>
    withLocalDecl n bi t fun x => view k cs (b.instantiate1 x)
  | 1 :: cs, .letE _ _ v _ _ => view k cs v
  | 2 :: cs, .letE n t v b nondep =>
    withLetDecl n t v (nondep := nondep) fun x => view k cs (b.instantiate1 x)
  | 0 :: cs, .proj _ _ s => view k cs s
  | cs, e => throwError "Invalid position {cs} in {e}"

def run (const : Name) (pos : Pos) (premises : NameSet) : MetaM Unit := do
  let value := (← getConstInfo const).value! (allowOpaque := true)
  view (fun e => do
    IO.println s!"Goal: {← ppExpr (← inferType e)}"
    let proofs ← canonicalSimple (← inferType e) premises (verbose := true) (witness := some e)
    if h : proofs.size > 0 then
      IO.println s!"Proof: {← ppExpr proofs[0]}"
    else
      IO.println "No proof found."
  ) pos.toArray.toList value

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
