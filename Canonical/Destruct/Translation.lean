module

import Lean
public import Lean.SubExpr
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
  /-- The position of `x` in `f (g x)` (β-reduced), if it occurs. -/
  cancelPos : Option SubExpr.Pos

partial def unfoldApply (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let .const name us := e.getAppFn | return e
  let info := ((← getEnv).find? name).get!
  let value := info.value! (allowOpaque := true)
  let value := value.instantiateLevelParams info.levelParams us
  unfoldApply (mkAppN value e.getAppArgs)

/-- The position of the first occurrence of `x` in `e`. -/
partial def findPos (x e : Expr) (pos : SubExpr.Pos := .root) : MetaM (Option SubExpr.Pos) := do
  if e == x then return some pos
  let (_, found) ← (traverseChildrenWithPos (M := StateT (Option SubExpr.Pos) MetaM) (fun pos c => do
    if (← get).isNone then set (← findPos x c pos)
    pure c) pos e).run none
  return found

def iff_to_translation {A B} (h : A ↔ B) : Translation A B :=
  ⟨h.mp, h.mpr⟩

instance {m} [Monad m] : MonadLift Option (OptionT m) where
  monadLift o := (pure o : m _)

def MetaTranslation.make (info : ConstantInfo) : OptionT MetaM MetaTranslation := do
  let value ← info.value? (allowOpaque := true)
  let head := info.type.getForallBody
  let .const headName headLevels := head.getAppFn | failure
  lambdaTelescope value fun fvars packed => do
    let target := (← inferType packed).getAppArgs[1]!
    let packed ← match headName with
    | ``Iff => some (mkAppN (.const ``iff_to_translation headLevels) (head.getAppArgs.push packed))
    | ``Translation => some (packed)
    | _ => none

    let isProj := ((← getEnv).isProjectionFn ·)
    let f ← deltaExpand (← unfoldApply (← project? packed 0)) isProj (allowOpaque := true)
    let g ← deltaExpand (← unfoldApply (← project? packed 1)) isProj (allowOpaque := true)
    -- The annotation keeps `none` from being lifted into a failure of `OptionT`.
    let cancelPos : Option SubExpr.Pos ← withLocalDeclD `x target fun x => do
      findPos x (← Core.betaReduce (apply f (apply g x)))

    return { f := ← mkLambdaFVars fvars f, g := ← mkLambdaFVars fvars g,
             type := info.type, levels := info.levelParams, cancelPos }

/-- Replace each subterm of the form `f (g x)` in `e` with `x`, for each of the `translations`. -/
def cancel (translations : Array MetaTranslation) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    for mt in translations do
      let some pos := mt.cancelPos | continue
      let some x ← (try pure (some (← Core.viewSubexpr pos e)) catch _ => pure none) | continue
      if x.hasLooseBVars then continue
      let levels ← mkFreshLevelMVars mt.levels.length
      let (params, _, translation) ← forallMetaTelescope (mt.type.instantiateLevelParams mt.levels levels)
      let f := applyN (mt.f.instantiateLevelParams mt.levels levels) params
      let g := applyN (mt.g.instantiateLevelParams mt.levels levels) params
      let input ← mkFreshExprMVar translation.getAppArgs[1]!
      if ← isDefEqGuarded input x then
        if ← isDefEqGuarded (← Core.betaReduce (apply f (apply g input))) e then
          return .done x
    return .continue)

noncomputable def translate_exists (α : Sort u) (p : α → Prop) : Translation (Exists p) { x : α // p x } :=
  ⟨
    fun e => { val := e.choose, property := e.choose_spec },
    fun e' => Exists.intro e'.val e'.property
  ⟩

noncomputable def translate_nonempty (α : Sort u) : Translation (Nonempty α) α :=
  ⟨fun e => Classical.choice e, fun e' => Nonempty.intro e'⟩

structure Unit' where

def translate_true : Translation True Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => True.intro⟩

def translate_unit : Translation Unit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => ()⟩

def translate_punit : Translation PUnit Unit' :=
  ⟨fun _ => Unit'.mk, fun _ => PUnit.unit⟩
