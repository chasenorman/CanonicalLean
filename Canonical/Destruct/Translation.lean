module

import Lean
public import Lean.Expr
public import Lean.Meta.Basic
public import Canonical.Destruct.Util

open Lean Core Meta

namespace Destruct

public section

/-- Forward and backwards maps between instances of `A` and `B`, where `A` is a
    sort appearing in a goal that we wish to replace with `B`.
-/
structure Translation (A : Sort u) (B : Sort v) where
  f : A → B
  g : B → A

-- Example translations:
structure Exists' (α : Sort u) (p : α → Prop) where
  value : α
  proof : p value

noncomputable def translate_exists (α : Sort u) (p : α → Prop) : Translation (Exists p) (Exists' α p) :=
  ⟨
    fun e => { value := e.choose, proof := e.choose_spec },
    fun e' => Exists.intro e'.value e'.proof
  ⟩

def TRANSLATION_STRUCTURES := #[``Exists']
def TRANSLATIONS : Array Name := #[``translate_exists]

def findTranslation (t : Expr) : MetaM (Option Name) := do
  -- TODO: check if t matches some left-hand-side of any Translation stored
  -- in TRANSLATIONS via syntactic matching
  -- (also think about if there are any problems that could come up with def
  -- equality)
  return .none
