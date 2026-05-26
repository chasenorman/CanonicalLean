module

public import Canonical.ToCanonical.Util
import Canonical.Monomorphize.Basic
import Canonical.ToCanonical.Translate
import Canonical.ToCanonical.Reduction
import Canonical.Symbols
import Lean

open Lean hiding Term
open Meta Expr Std Monomorphize

namespace Canonical

public section

/-- Attempt to include a premise of type `type` as a reduction rule, instead of a definiton.
    Returns `true` if successful. -/
def registerSimpPremise (attribution : String) (type : Expr) : ToCanonicalM Bool := do
  if (← read).config.simp then
    if let some rule ← toRule #[attribution] type false then
      if ← addConstraints #[rule] then
        modify fun s =>
          let defn := (s.definitions.find? rule.lhs.head).get!
          { s with
            definitions := s.definitions.insert rule.lhs.head { defn with
              rules := defn.rules.push rule
            }
          }
        return true
  return false

/-- Add premise `name`, monomorphizing and/or registering as a simp lemma if appropriate. -/
def definePremise (const : Name) (simpOnly : Bool := false) : ToCanonicalM Unit := do
  let (modified1, monomorphized) ← monomorphizePremise const
  for premise in monomorphized do
    let (modified2, destructed) ← destructPremise const premise simpOnly
    for (_expr, type, name) in destructed do
      if !(← registerSimpPremise const.toString type) && !simpOnly then
        if !modified1 && !modified2 then let _ ← defineConst const
        else let _ ← define name.toString type

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

def toCanonical_ (goal : Expr) (premises : Array Name) : ToCanonicalM Typ := do
  -- Local Context
  let lets : Array (Let × Option Typ) := ← withReader (fun ctx => { ctx with polarity := .premise }) do
    (← getLCtx).foldlM (fun lets decl => do
      if !decl.isAuxDecl then
        let (name, type) ← toHead decl.toExpr
        if let some value := decl.value? then
          let rule := defRule name.toString (← toTerm value type (← typeArity type).params.toList)
          pure (lets.push ⟨{ name := name.toString, rules := #[rule] }, none⟩)
        else
          pure (lets.push ⟨{ name := name.toString }, ← toBind decl.fvarId⟩)
      else pure lets
    ) #[]

  -- Goal Type
  let typ ← toTyp goal

  -- Constant Symbol Premises
  withReader (fun ctx => { ctx with polarity := .premise }) do
    for premise in premises do
      let _ ← definePremise premise

  -- Simp Lemmas
  if (← read).config.simp then
    let _ ← addSimpLemmas

  let lets := lets ++ (← get).definitions.toList.toArray.map fun ⟨name, defn⟩ => ({ name, rules := defn.rules }, defn.type.toOption)

  let _ ← finalizeMonos

  return { typ with
    letTypes := lets.map Prod.snd ++ typ.letTypes,
    lets := lets.map Prod.fst ++ typ.lets
  }

/-- Convert `goal` to a `Typ` with `premises` and all included definitions. -/
def toCanonical (goal : Expr) (premises : Array Name) (structures : Array Name) (config : CanonicalConfig) : MetaM Typ := do
  let lctx ← getLCtx
  (((toCanonical_ goal premises).run
    {
      arities := ← lctx.foldlM (fun arities decl => do
        pure (arities.insert decl.fvarId (← typeArity decl.type)))
          (.emptyWithCapacity lctx.size), config, structures
    }).run' { }).run'
      { globalFVars := .ofArray lctx.getFVarIds, constNames := .ofList [``OfNat.ofNat] }
