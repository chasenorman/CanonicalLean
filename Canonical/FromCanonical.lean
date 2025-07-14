import Canonical.Basic
import Canonical.ToCanonical
import Lean

namespace Canonical

open Lean hiding Term
open Std Meta Syntax

/-- When translating from Canonical, we associate names in the `Term` with corresponding Lean `FVarId`s -/
abbrev FromCanonicalM := StateT (HashMap String FVarId) MetaM

partial def removePi (t : Term) : Term :=
  if t.spine.head == (``Pi.mk).toString then
    let body := t.spine.args[2]!
    removePi { params := t.params ++ body.params, lets := t.lets ++ body.lets, spine := body.spine }
  else if t.spine.head == (``Pi.f).toString then
    let fn := t.spine.args[2]!
    let arg := t.spine.args[3]!
    removePi { params := t.params ++ fn.params, lets := t.lets ++ fn.lets,
               spine := { fn.spine with args := fn.spine.args.push arg } }
  else t

/- Inverse of `toHead` in `Util.lean`. -/
def fromHead (s : String) : FromCanonicalM (Expr × Expr) := do
  if s == (`Sort).toString then
    let l ← mkFreshLevelMVar
    return (.sort l, .sort l.succ)
  else if let some n := s.toNat? then
    return (mkNatLit n, .const ``Nat [])
  else if let some s := decodeStrLit s then
    return (mkStrLit s, .const ``String [])
  else if let some info := (← getEnv).find? s.toName then
    return (← mkConstWithFreshMVarLevels info.name, info.type)
  else if let some id := (← get).get? s then
    return (.fvar id, ← id.getType)
  else if let some id := (← getMCtx).findUserName? s.toName then
    return (← instantiateMVars (.mvar id), ← id.getType)
  else
    let name := (s.dropWhile (!·.isAlphanum)).takeWhile (·.isAlphanum)
    return (← mkFreshExprMVar none (userName := name.toName), .sort .zero)

mutual
  partial def fromTerm (t : Term) (type : Expr) : FromCanonicalM Expr := do
    forallTelescopeReducing type fun xs _ => do
      let t := removePi t
      assert! xs.size == t.params.size
      let ids := xs.map (fun x => x.fvarId!)
      let names := t.params.map (fun v => v.name)
      modify (·.insertMany (names.zip ids))
      mkLambdaFVars xs (← fromSpine t.spine)

  partial def fromSpine (s : Spine) : FromCanonicalM Expr := do
    if s.head == (``Pi).toString then
      let binderType ← fromTerm s.args[0]! (.sort (← mkFreshLevelMVar))
      let lam ← fromTerm s.args[1]! (.forallE `a binderType (.sort (← mkFreshLevelMVar)) .default)
      if let .lam a b c d := lam then
        return (.forallE a b c d)
      else throwError "Failure to convert Pi to forallE."
    let (fn, fnType) ← fromHead s.head
    return mkAppN fn (← fromApp s.args.toList fnType).toArray

  partial def fromApp (args : List Term) (type : Expr) : FromCanonicalM (List Expr) := do
    match ← whnf type with
    | .forallE _ binderType body _ =>
      let arg ← fromTerm (args.head!) binderType
      return arg :: (← fromApp args.tail! (body.instantiate1 arg))
    | _ =>
      assert! args.isEmpty
      return []
end

def fromCanonical (t : Term) (type : Expr) : MetaM Expr := do
  return ← (fromTerm t type).run' (← (← getLCtx).foldlM (fun acc decl =>
    do pure (acc.insert (← toHead decl.toExpr).1.toString decl.fvarId)) {})
