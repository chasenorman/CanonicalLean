import Canonical.Basic
import Canonical.ToCanonical
import Lean

namespace Canonical

open Lean hiding Term
open Std Meta Syntax

/-- When translating from Canonical, we associate names in the `Term` with corresponding Lean `FVarId`s -/
abbrev FromCanonicalM := StateT (HashMap String FVarId) MetaM

/-- Converts instances of `Pi.mk` and `Pi.f` at the head into λ-expressions and applications, respectively. -/
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

open PrettyPrinter Delaborator SubExpr in
/-- We use `.mdata` to store information about tactics used by Canonical. -/
@[delab mdata.canonical]
def delabCanonical : Delab := do
  match ← getExpr with
  | .mdata map _ =>
    let result ← (map.getSyntax `canonical).replaceM (fun x =>
      if x.isMissing then withMDataExpr delab else pure none)
    pure (TSyntax.mk result)
  | _ => throwError "delabCanonical called on non-mdata"

/-- Syntax for `simp` and `simpa` calls generated given the `premiseRules` and `goalRules` attribution. -/
def toSyntax (premiseRules: Array String) (goalRules: Array String) : Syntax := Unhygienic.run do
  let premiseRules := premiseRules.toList.toSSet.toList.toArray
  let goalRules := goalRules.toList.toSSet.toList.toArray
  let result ← if premiseRules.isEmpty then `(tacticSeq| exact $(TSyntax.mk .missing)) else
    let cc : Array (TSyntax `ident) := premiseRules.map (fun s => mkIdent s.toName)
    `(tacticSeq| simpa only [$[$cc:ident],*] using $(TSyntax.mk .missing))
  let result ← if goalRules.isEmpty then
    `(term| by $result)
  else do
    let cc : Array (TSyntax `ident) := goalRules.map (fun s => mkIdent s.toName)
    `(term| by simp only [$[$cc:ident],*] <;> $(TSyntax.mk result))
  pure result

/- Inverse of `toHead` in `Util.lean`. -/
def fromHead (s : String) : FromCanonicalM (Expr × Expr) := do
  if s == (`Sort).toString then
    let l ← mkFreshLevelMVar
    return (.sort l, .sort l.succ)
  else if let some n := s.toNat? then
    return (mkNatLit n, .const ``Nat [])
  else if s.startsWith "\"" && s.endsWith "\"" then
    return (mkStrLit ((s.drop 1).dropRight 1), .const ``String [])
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
  /-- Builds a λ-expression of type `type` following the parameters of `t`. -/
  partial def fromTerm (t : Term) (type : Expr) : FromCanonicalM Expr := do
    forallTelescopeReducing type fun xs body => do
      let t := removePi t
      assert! xs.size == t.params.size
      let ids := xs.map (fun x => x.fvarId!)
      let names := t.params.map (fun v => v.name)
      modify (·.insertMany (names.zip ids))

      let spine ← if t.spine.head == "<synthInstance>" then do
        if let .some result ← trySynthInstance body then pure result
          else pure (← mkFreshExprMVar none)
      else fromSpine t.spine

      let premiseRules := if ← t.spine.premiseRules.allM (fun s => do isRflTheorem s.toName) then #[] else t.spine.premiseRules
      let goalRules := if ← t.goalRules.allM (fun s => do isRflTheorem s.toName) then #[] else t.goalRules

      if (!premiseRules.isEmpty || !goalRules.isEmpty) then
        return ← mkLambdaFVars xs (.mdata (KVMap.empty.insert `canonical (.ofSyntax (toSyntax premiseRules goalRules))) spine)
      else return ← mkLambdaFVars xs spine

  /-- Builds an application expression from `s`. -/
  partial def fromSpine (s : Spine) : FromCanonicalM Expr := do
    if s.head == (``Pi).toString then
      let binderType ← fromTerm s.args[0]! (.sort (← mkFreshLevelMVar))
      let lam ← fromTerm s.args[1]! (.forallE `a binderType (.sort (← mkFreshLevelMVar)) .default)
      if let .lam a b c d := lam then
        return (.forallE a b c d)
      else throwError "Failure to convert Pi to forallE."
    let (fn, fnType) ← fromHead s.head
    return ← whnf (mkAppN fn (← fromApp s.args.toList fnType).toArray)

  /-- Recursively translates the arguments of a head symbol with type `type`.  -/
  partial def fromApp (args : List Term) (type : Expr) : FromCanonicalM (List Expr) := do
    match ← whnf type with
    | .forallE _ binderType body _ =>
      let arg ← fromTerm (args.head!) binderType
      return arg :: (← fromApp args.tail! (body.instantiate1 arg))
    | _ =>
      assert! args.isEmpty
      return []
end

/-- Converts a Term `t` of type `type` to a Lean expression. -/
def fromCanonical (t : Term) (type : Expr) : MetaM Expr := do
  return ← (fromTerm t type).run' (← (← getLCtx).foldlM (fun acc decl =>
    do pure (acc.insert (← toHead decl.toExpr).1.toString decl.fvarId)) {})
