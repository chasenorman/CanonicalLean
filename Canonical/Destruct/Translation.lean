module

import Lean
public import Lean.Expr
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

-- Is this useful at all? x ≥ y is an abbreviation for y ≤ x anyway.
def translate_le {α} [LE α] (x : α) (y : α) : Translation (x ≥ y) (y ≤ x) :=
  ⟨fun a => a, fun a => a⟩

-- Ideas:
-- Perhaps mapping x^2 to x * x?
-- x % 2 = 0 to Even x

def TRANSLATION_STRUCTURES := #[``Exists', ``Unit']
def TRANSLATIONS : Array Name := #[``translate_exists, ``translate_true, ``translate_unit, ``translate_punit, ``translate_le]

partial def syntacticMatch (raw : Expr) (pattern : Expr) : StateT (HashMap FVarId Expr) MetaM (Option Unit) := do
  match (raw.consumeMData, pattern.consumeMData) with
  | (Expr.const rawName rawLevels, Expr.const patName patLevels) => do
    if rawName != patName then return .none
    for (l, l') in (rawLevels.zip patLevels) do
      -- Claim: This (hopefully) shouldn't be expensive since the left-hand-side
      -- levels should be concrete, constant values
      if !(← isLevelDefEq l l') then return .none
  | (_, Expr.fvar id) => do
    let state ← get
    if state.contains id then
      if raw != state.get! id then return .none
    else
      set (state.insert id raw)
  | (Expr.lam _ rawType rawBody rawInfo, Expr.lam _ patType patBody patInfo) => do
    if rawInfo != patInfo then return .none
    if (← syntacticMatch rawType patType).isNone then return .none
    if (← syntacticMatch rawBody patBody).isNone then return .none
  | (Expr.forallE _ rawType rawBody rawInfo, Expr.forallE _ patType patBody patInfo) => do
    if rawInfo != patInfo then return .none
    if (← syntacticMatch rawType patType).isNone then return .none
    if (← syntacticMatch rawBody patBody).isNone then return .none
  | (Expr.app rawFn rawArg, Expr.app patFn patArg) => do
    if (← syntacticMatch rawFn patFn).isNone then return .none
    if (← syntacticMatch rawArg patArg).isNone then return .none
  | (Expr.sort rawLevel, Expr.sort patLevel) => do
    -- Perhaps this should just be syntactic equality?
    if !(← isLevelDefEq rawLevel patLevel) then return .none
  | (Expr.proj rawName rawInd rawStruct, Expr.proj patName patInd patStruct) => do
    if rawName != patName then return .none
    if rawInd != patInd then return .none
    if (← syntacticMatch rawStruct patStruct).isNone then return .none
  | _ => if raw != pattern then return .none

-- TODO: think through whether this is actually correct (worried a little about
-- how levels are treated but hopefully this is okay)
def findTranslation (t : Expr) : MetaM (Option (Expr × Expr)) := do
  TRANSLATIONS.findSomeM? fun name => do
    let head ← mkConstWithFreshMVarLevels name
    let type ← inferType head
    forallTelescope type fun fvars translation => do
      let pattern := translation.getAppArgs[0]!
      let replace := translation.getAppArgs[1]!
      if let (.some _, map) ← (syntacticMatch t pattern).run (HashMap.emptyWithCapacity fvars.size) then
        let assignments := fvars.map (map.get! ·.fvarId!)
        let replaced := replace.replaceFVars fvars assignments
        let translated := mkAppN head assignments
        return .some (replaced, translated)
      return .none
