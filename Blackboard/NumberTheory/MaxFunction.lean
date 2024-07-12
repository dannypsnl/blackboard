import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Group.Units

example (a b : ℕ) :
  (max a b) = a ∨ (max a b) = b
  := by
  simp
  exact Nat.le_total b a
