module

import Lean
public import Canonical.Destruct.Util

open Lean Meta

namespace Destruct

public section

/-- Forward and backwards maps between instances of `A` and `B`, where `A` is a
    sort appearing in a premise or goal that we wish to replace with `B`. -/
structure Translation (A : Sort u) (B : Sort v) where
  f : A → B
  g : B → A

/-- `Translation` meta-objects that are computable expressions. This structure
    stores the necessary info (levels, type, etc.) in order to instantiate the
    value.  -/
structure MetaTranslation where
  f : Expr
  g : Expr
  type : Expr
  levels : List Name

partial def unfoldApply (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let .const name us := e.getAppFn | return e
  let info := ((← getEnv).find? name).get!
  let value := info.value! (allowOpaque := true)
  let value := value.instantiateLevelParams info.levelParams us
  unfoldApply (mkAppN value e.getAppArgs)

def iff_to_translation {A B} (h : A ↔ B) : Translation A B :=
  ⟨h.mp, h.mpr⟩

instance {m} [Monad m] : MonadLift Option (OptionT m) where
  monadLift o := (pure o : m _)

def MetaTranslation.make (info : ConstantInfo) : OptionT MetaM MetaTranslation := do
  let value ← info.value? (allowOpaque := true)
  let head := info.type.getForallBody
  let .const headName headLevels := head.getAppFn | failure
  lambdaTelescope value fun fvars packed => do
    let packed ← match headName with
    | ``Iff => some (mkAppN (.const ``iff_to_translation headLevels) (head.getAppArgs.push packed))
    | ``Translation => some (packed)
    | _ => none

    let f ← mkLambdaFVars fvars (← unfoldApply (← project? packed 0))
    let g ← mkLambdaFVars fvars (← unfoldApply (← project? packed 1))

    return { f, g, type := info.type, levels := info.levelParams }

noncomputable def translate_exists (α : Sort u) (p : α → Prop) : Translation (Exists p) { x : α // p x } :=
  ⟨
    fun e => { val := e.choose, property := e.choose_spec },
    fun e' => Exists.intro e'.val e'.property
  ⟩

structure Unit' where

def translate_true : Translation True Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => True.intro⟩

def translate_unit : Translation Unit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => ()⟩

def translate_punit : Translation PUnit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => PUnit.unit⟩
