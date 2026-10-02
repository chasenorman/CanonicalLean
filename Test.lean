import Canonical

-- structure Eventually (p : Nat → Prop) where
--   proof : ∀ (n : Nat), ∃ (k : Nat), k ≥ n ∧ p k
--
-- def translate_eventually (p : Nat → Prop) : (Eventually p) ↔

theorem translate_rfl (α : Sort u) (x : α) : Iff (x = x) True :=
  ⟨fun _ => True.intro, fun _ => rfl⟩

example : ∃ x : Unit, x = x := by
  destruct [translate_rfl]

def translate_ge (a : Nat) (b : Nat) : a ≥ b ↔ b ≤ a := by
  simp

example : 3 ≥ 2 := by
  destruct


def test (p : ∃ n : Nat, n = n) : (∃ n : Nat, n = n) := by
  destruct
