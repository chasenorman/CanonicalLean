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
    sort appearing in a premise or goal that we wish to replace with `B`.
-/
structure Translation (A : Sort u) (B : Sort v) where
  f : A → B
  g : B → A

def iff_to_translation {A B} (h : A ↔ B) : Translation A B :=
  ⟨h.mp, h.mpr⟩

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

-- Ideas:
-- x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B (same thing for ∨ and \ operators)
-- Set equality via double containment (actually this is provided by ext)
-- Unfolding the subseteq definition
-- Translating decidable propositions?

-- Remember to update these after defining a new translation!
def TRANSLATIONS : Array Name := #[``translate_exists, ``translate_true, ``translate_unit, ``translate_punit]

-- Returns the replaced expression as well as the Translation.
def matchTranslation (t : Expr) : MetaM (Option (Expr × Expr)) := withTransparency .none do
  for name in TRANSLATIONS do
    let head ← mkConstWithFreshMVarLevels name
    let type ← inferType head
    let (mvars, _, translation) ← forallMetaTelescope type
    let pattern := translation.getAppArgs[0]!
    let replace := translation.getAppArgs[1]!
    if ← isDefEqGuarded t pattern then
      let replaced ← instantiateMVars replace
      let translated ← instantiateMVars (mkAppN head mvars)
      return .some (replaced, translated)
  return .none
