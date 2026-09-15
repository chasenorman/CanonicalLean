import Canonical

-- example : Nat := by canonical

-- example : ∃ (t : Type 10), True := by
--   destruct
--   · exact Type 9
--
-- example : ∃ (t : Unit), True := by
--   destruct

-- example : (fun x y => (x * y, y)) 2 3 = (6, 3) := by
--   have h0 : True := by trivial
--   destruct
--   · rfl
--   · rfl

-- example : (fun (x : Nat) => 3) = (fun (y : Nat) => 2 + 1) := by
--   destruct
--   intro _
--   rfl
-- partial def fib : Nat → Nat
--   | 0 => 0
--   | 1 => 1
--   | n => fib (n - 1) + fib (n - 2)
--
-- example : (fib 0, fib 1, fib 2, fib 3) = (0, 1, 1, 2) := by
--   have h0 : fib 0 = 0 := by sorry
--   have h1 : fib 1 = 1 := by sorry
--   have h2 : fib 2 = 1 := by sorry
--   have h3 : fib 3 = 2 := by sorry
--   destruct
--   · simp
--     exact h0
--   · simp
--     exact h1
--   · simp
--     exact h2
--   · simp
--     exact h3

-- example (A : Array Unit) (B : Array Unit) (h : A.size = B.size) : A = B := by
--   destruct
--   exact h
