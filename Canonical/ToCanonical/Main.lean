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

/-- Replace each destructed premise with `pack` of its component metavariables. -/
def substDestructed (destructed : Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) (e : Lean.Expr) :
    MetaM Lean.Expr := do
  let mut e := e
  for (premise, pack, metas) in destructed do
    -- Monomorphized premises are not yet supported.
    let .const name _ := premise | continue
    e ← Meta.transform e (post := fun x => do
      if x.isConstOf name && (← isDefEq x premise) then
        return .done (Destruct.applyN pack metas)
      return .continue)
  return e

/-- Translate `witness`, a proof of `goal`, into the problem built so far,
    given the premises that were `destructed`. -/
def witnessToCanonical (goal witness : Lean.Expr) (destructed : Array (Lean.Expr × Lean.Expr × Array Lean.Expr)) :
    ToCanonicalM Canonical.Expr := do
  let witness ← Core.betaReduce (← substDestructed destructed witness)
  let witness ← Destruct.cancel (← read).destruct.translations witness
  let witness ← Destruct.reduceProjs witness
  let witness ← Meta.transform witness (post := fun e => return .done (← whnf e))
  toTerm witness goal (← typeArity goal).params.toList

def toCanonical_ (name : String) (goal : Lean.Expr) (premises : Array Name) (witness : Option Lean.Expr := none) :
    ToCanonicalM (Decl × Option Canonical.Expr) := do
  -- Local Context
  let lets ← withReader (fun ctx => { ctx with polarity := .premise }) do
    (← getLCtx).foldlM (init := #[]) fun lets decl =>
      if decl.isAuxDecl then pure lets else lets.push <$> toDecl decl.fvarId

  -- Goal Type
  let type ← toType goal

  -- Constant Symbol Premises
  let destructed ← withReader (fun ctx => { ctx with polarity := .premise }) do
    premises.foldlM (init := #[]) fun destructed premise => do
      pure (destructed ++ (← definePremise premise))

  -- Simp Lemmas
  if (← read).config.simp then
    let _ ← addSimpLemmas

  let lets := lets ++ (← get).definitions.toList.toArray.map fun ⟨name, defn⟩ =>
    { name, equations := defn.equations, type := defn.type.toOption }

  let witness ← try witness.mapM (witnessToCanonical goal · destructed) catch _ => pure none

  let _ ← finalizeMonos

  return ({ name, type := some { type with lets := lets ++ type.lets } }, witness)

/-- Convert `goal` to a `Decl` named `name`, with `premises` and all included definitions.
    If given `witness`, a proof of `goal`, also translates it into the resulting problem. -/
def toCanonical (name : String) (goal : Lean.Expr) (premises : Array Name) (structures : Array Name) (config : Config)
    (witness : Option Lean.Expr := none) : MetaM (Decl × Option Canonical.Expr) := do
  let lctx ← getLCtx
  (((toCanonical_ name goal premises witness).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size), config
      destruct := ← Destruct.Context.populate structures
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds, constNames := .ofList [``OfNat.ofNat] }
