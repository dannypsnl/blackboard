import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

theorem multiply_two_neighbors_is_even
  (n : ℕ)
  : Even (n * (n + 1))
  := by
  have P := Nat.even_or_odd n
  induction P
  . exact Nat.even_mul_succ_self n
  . exact Nat.even_mul_succ_self n
