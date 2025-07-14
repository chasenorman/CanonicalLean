import Canonical.Main

def test : 0 + n = n :=
  by canonical [Nat.add_zero, Nat.add_succ]
