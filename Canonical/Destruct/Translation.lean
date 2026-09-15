module

import Lean
public import Lean.Expr
public import Lean.Meta.Tactic.Ext
public import Lean.Meta.Basic
public import Canonical.Destruct.Util

open Std Lean Core Meta

namespace Destruct

public section

/-- Forward and backwards maps between instances of `A` and `B`, where `A` is a
    sort appearing in a goal that we wish to replace with `B`.
-/
structure Translation (A : Sort u) (B : Sort v) where
  f : A → B
  g : B → A

def iff_to_translation (h : A ↔ B) : Translation A B :=
  ⟨h.mp, h.mpr⟩

-- Example translations:
structure Exists' (α : Sort u) (p : α → Prop) where
  value : α
  proof : p value

noncomputable def translate_exists (α : Sort u) (p : α → Prop) : Translation (Exists p) (Exists' α p) :=
  ⟨
    fun e => { value := e.choose, proof := e.choose_spec },
    fun e' => Exists.intro e'.value e'.proof
  ⟩

structure Unit' where

def translate_true : Translation True Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => True.intro⟩

def translate_unit : Translation Unit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => ()⟩

def translate_punit : Translation PUnit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => PUnit.unit⟩

def translate_ge {α} [LE α] (x : α) (y : α) : Translation (y ≥ x) (x ≤ y) :=
  ⟨fun a => a, fun a => a⟩

-- Should we unfold Not?
def translate_ne {α} (x : α) (y : α) : Translation (x ≠ y) (¬(x = y)) :=
  ⟨fun a => a, fun a => a⟩

-- def translate_decidable (p : Prop) [h : Decidable p] : Translation p (decide p)

-- Ideas:
-- x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B (same thing for ∨ and \ operators)
-- Maybe also set equality via double containment
-- Also like ⊇

-- Remember to update these after defining a new translation!
def TRANSLATION_STRUCTURES := #[``Exists', ``Unit']
def TRANSLATIONS : Array Name := #[``translate_exists, ``translate_true, ``translate_unit, ``translate_punit, ``translate_ge, ``translate_ne]

def matchExt (t : Expr) : MetaM (Option (Expr × Expr)) := do
  let head := t.getAppFn
  let args := t.getAppArgs
  let env ← getEnv

  if head.constName != `Eq then return .none
  if args.size != 3 then return .none

  let t' := args[0]!.headBeta
  let extTheorems ← Ext.getExtTheorems t'
  for extTheorem in extTheorems do
    -- I believe this is how ext generates ext_iff theorems so we should be fine
    -- to do this.
    let iffName := (extTheorem.declName.toString ++ "_iff").toName
    if !(env.contains iffName) then continue
    let iffTheorem ← mkConstWithFreshMVarLevels iffName
    let iffType ← inferType iffTheorem
    let (mvars, _, iff) ← forallMetaTelescope iffType
    let pattern := iff.getAppArgs[0]!
    let replace := iff.getAppArgs[1]!
    if (← isDefEq t pattern) then do
      let pattern ← instantiateMVars pattern
      let replace ← instantiateMVars replace
      let iffTheorem ← instantiateMVars (mkAppN iffTheorem mvars)
      let translation := mkAppN (Expr.const ``iff_to_translation []) #[pattern, replace, iffTheorem]
      return .some (replace, translation)
  return .none

-- Returns the replaced expression as well as the Translation.
def matchTranslation (t : Expr) : MetaM (Option (Expr × Expr)) := do
  withTransparency .none do
  if let .some (replaced, translation) ← matchExt t then
    return .some (replaced, translation)
  TRANSLATIONS.findSomeM? fun name => do
    let head ← mkConstWithFreshMVarLevels name
    let type ← inferType head
    let (mvars, _, translation) ← forallMetaTelescope type
    let pattern := translation.getAppArgs[0]!
    let replace := translation.getAppArgs[1]!
    if (← isDefEq t pattern) then
      let replaced ← instantiateMVars replace
      let translated ← instantiateMVars (mkAppN head mvars)
      return .some (replaced, translated)
    return .none
