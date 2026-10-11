module

public import Canonical.ToCanonical.Util
import Canonical.ToCanonical.Translate
import Canonical.ToCanonical.Reduction
import Canonical.Destruct.Basic
import Lean

open Lean
open Meta Expr Std Monomorphize

namespace Canonical

public section

/-- Attempt to include a premise of type `type` as a reduction rule, instead of a definiton.
    Returns `true` if successful. Otherwise, the symbols defined by the attempt are discarded. -/
def registerSimpPremise (attribution : String) (type : Lean.Expr) (simpOnly : Bool) : ToCanonicalM Bool := do
  if (← read).config.simp then
    let (state, monoState) := (← get, ← getThe MonoState)
    if let some rule ← toRule #[attribution] type false then
      if (!simpOnly || state.definitions.contains rule.lhs.head) && (← addConstraints #[rule]) then
        addEquations rule.lhs.head #[rule]
        return true
    set state; set monoState
  return false

/-- Add premise `name`, monomorphizing and/or registering as a simp lemma if appropriate.
    Returns each destructed premise expression, with its `pack` and component metavariables. -/
def definePremise (const : Name) (simpOnly : Bool := false) :
    ToCanonicalM (Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) := do
  let (modified1, monomorphized) ← monomorphizePremise const
  let mut destructedPremises := #[]
  for (expr, type, name) in monomorphized do
    if !(← registerSimpPremise const.toString type simpOnly) && !simpOnly then
      let (bij?, destructed) ← destructPremise const expr type name simpOnly
      if let some (pack, metas) := bij? then
        destructedPremises := destructedPremises.push (expr, pack, metas)
      for (_expr, type, name) in destructed do
        if !modified1 && bij?.isNone then let _ ← defineConst const
        else let _ ← define name.toString type
  return destructedPremises

def addSimpLemmas : ToCanonicalM Unit := do
  withReader (fun ctx => { ctx with polarity := .premise }) do
    let mut attempted ← getConstants
    -- Adding `simp` lemmas may introduce new definitions, making more `simp` lemmas relevant.
    while ← consumeNewConstFlag do
      let thms ← getRelevantSimpTheorems (← getConstants)
      for thm in thms do
        if !attempted.contains thm then
          attempted := attempted.insert thm
          let _ ← definePremise thm true

def toCanonical_ (name : String) (goal : Lean.Expr) (premises : Array Name) : ToCanonicalM Decl := do
  -- Local Context
  let lets ← withReader (fun ctx => { ctx with polarity := .premise }) do
    (← getLCtx).foldlM (init := #[]) fun lets decl =>
      if decl.isAuxDecl then pure lets else lets.push <$> toDecl decl.fvarId

  -- Goal Type
  let type ← toType goal

  -- Constant Symbol Premises
  withReader (fun ctx => { ctx with polarity := .premise }) do
    premises.forM fun premise => do
      let _ ← definePremise premise

  -- Simp Lemmas
  if (← read).config.simp then
    let _ ← addSimpLemmas

  let lets := lets ++ (← get).definitions.toList.toArray.map fun ⟨name, defn⟩ =>
    { name, equations := defn.equations, type := defn.type.toOption }

  let _ ← finalizeMonos

  return { name, type := some { type with lets := lets ++ type.lets } }

/-- Convert `goal` to a `Decl` named `name`, with `premises` and all included definitions. -/
def toCanonical (name : String) (goal : Lean.Expr) (premises : Array Name) (structures : Array Name) (config : Config) : MetaM Decl := do
  let lctx ← getLCtx
  (((toCanonical_ name goal premises).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size), config
      destruct := ← Destruct.Context.populate structures
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds, constNames := .ofList [``OfNat.ofNat] }
