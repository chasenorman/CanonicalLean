import Canonical

-- example : Nat := by canonical

def translate_rfl (α : Sort u) (x : α) : Destruct.Translation (x = x) True :=
  ⟨fun _ => True.intro, fun _ => rfl⟩

example : ∃ x : Unit, x = x := by
  destruct [translate_rfl]
