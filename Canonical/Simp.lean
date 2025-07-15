import Lean
import Canonical.Util

open Lean Meta Std DiscrTree Trie Key Expr

namespace Canonical

def SIMP_HARD_CODE : HashMap Name (Array Name) := .ofList [
  (`Nat.succ_eq_add_one, #[`Nat.succ.injEq]),
  (`Nat.add_zero, #[`Nat.add_zero, `Nat.add_succ, `Nat.succ_add, `Nat.add_assoc]),
  (`Nat.mul_one, #[]),
  (`Nat.one_mul, #[`Nat.succ_mul, `Nat.mul_assoc]),
  (`Nat.one_pow, #[`Nat.pow_succ, `Nat.pow_add, `Nat.mul_pow]),
  (`Nat.pow_one, #[]),
]

/-- Retrieves the `Origin`s in `trie` consisting only of constants in `constSet`.  -/
partial def getOrigins (constSet : NameSet) (trie : Trie SimpTheorem) : Array Origin :=
  match trie with
  | node vs children =>
    let filtered := children.filter fun child =>
      match child.1 with
      | .proj name _ _ | .const name _ => constSet.contains name
      | .arrow => false
      | _ => true
    (vs.filterMap (fun x => if x.priority ≥ eval_prio default then some x.origin else none)) ++ filtered.flatMap (fun x => getOrigins constSet x.2)


def getRelevantSimpTheorems (constSet : NameSet) : MetaM (Array Name) := do
  let thms ← getSimpTheorems
  let tries ← constSet.toArray.filterMapM fun x => do
    pure (thms.post.root.find? (.const x (← typeArity1 (← getConstInfo x).type)))
  let origins := tries.flatMap (getOrigins constSet)
  let names := origins.filterMap fun x =>
    if let .decl name _ _ := x then some name else none
  let relevant ← names.filterM fun x => do
    forallTelescopeReducing (← getConstInfo x).type fun _ body => do
      if let some (_, lhs, _) := (eq? body) then do
        (lhs.getUsedConstantsAsSet.diff constSet).foldM (fun acc name => do
          pure (acc && (← getUnfoldableConst? name).isSome)
        ) true
      else pure false
  pure (relevant.flatMap fun x => SIMP_HARD_CODE.getD x #[x])
