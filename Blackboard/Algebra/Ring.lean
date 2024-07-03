import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Defs

theorem distribute_on_2 {R : Type u} [Ring R]
  (a b : R)
  : 2 * (a * b) = (2 * a) * b
  := by
  simp [two_mul]
  rw [Distrib.right_distrib]

theorem general_distribute {R : Type u} [Ring R]
  (m : Int)
  (a b : R)
  : m * (a * b) = (m * a) * b
  := by
  exact Eq.symm (mul_assoc (↑m) a b)
