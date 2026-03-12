module

public import Lean.PrettyPrinter.Delaborator.Basic
public meta import Lean.Data.KVMap
public meta import Lean.Exception
public meta import Lean.CoreM
public meta import Lean.PrettyPrinter.Delaborator.SubExpr
public meta import Lean.PrettyPrinter.Delaborator.Basic

open Lean Meta Expr Name

namespace Canonical

/-- Indicator for STAR type. -/
@[reducible, expose] public def STAR (α : Sort u) : Sort u := α

@[expose] public def dneg (Goal : Sort u) (destruct : (Destruct : STAR (Sort u)) → (Goal → Destruct) → Destruct) : Goal :=
  destruct Goal fun a ↦ a

@[expose] public def identity (name : Name) (e : Expr) : Expr := .lam name e (.bvar 0) .default

/-- Some Lean Π-types cannot be converted into Canonical Π-types,
    and are instead converted into this structure. -/
public structure Pi (A : Type u) (B : A → Type v) where
  f : (a : A) → B a

open PrettyPrinter Delaborator SubExpr in
/-- We use `.mdata` to store information about tactics used by Canonical. -/
@[delab mdata.canonical]
public meta def delabCanonical : Delab := do
  match ← getExpr with
  | .mdata map _ =>
    let result ← (map.getSyntax `canonical).replaceM (fun x =>
      if x.isMissing then withMDataExpr delab else pure none)
    pure (TSyntax.mk result)
  | _ => throwError "delabCanonical called on non-mdata"
