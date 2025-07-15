import Canonical.Main

inductive MyNat
| zero : MyNat
| succ : MyNat → MyNat

open MyNat

def MyNat.add : MyNat → MyNat → MyNat
| n, zero => n
| n, succ m => succ (n.add m)

theorem zero_add : zero.add n = n := by
  exact
    rec (motive := fun t ↦ zero.add t = t) (Eq.refl zero)
      (fun a a_ih ↦
        Eq.rec (motive := fun a_1 t ↦ (zero.add a).succ = a_1.succ) (Eq.refl (zero.add a).succ)
          a_ih)
      n

theorem succ_add : (succ n).add m = succ (n.add m) := by
  exact
    rec (motive := fun t ↦ n.succ.add t = (n.add t).succ) (Eq.refl n.succ)
      (fun a a_ih ↦
        Eq.rec (motive := fun a_1 t ↦ (n.succ.add a).succ = a_1.succ) (Eq.refl (n.succ.add a).succ)
          a_ih)
      m

theorem add_comm (n m : MyNat) : n.add m = m.add n := by
  exact
    rec (motive := fun t ↦ t.add m = m.add t)
      (by simp only [MyNat.add.eq_1, zero_add] <;> exact Eq.refl m)
      (by simp only [MyNat.succ.injEq, succ_add, MyNat.add.eq_2] <;> exact fun a a_ih ↦ a_ih) n


def test (x : Nat) : 2^x = 2^x := by canonical
