import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.BooleanRing

variable [BooleanRing A]

theorem add_in_boolean_ring
  : ∀ a : A, a + a = 0 := by
  intro a
  have := by calc
    a + a = (a + a) * (a + a) := by rw [BooleanRing.mul_self (a + a)]
    _ = a * a + a * a + a * a + a * a := by
      rw [right_distrib]
      rw [left_distrib]
      exact Eq.symm (add_rotate (a * a + a * a) (a * a) (a * a))
    _ = a + a + a + a := by rw [BooleanRing.mul_self a]
  simp at this
  exact this

lemma neg_eq : ∀ a : A, -a = a := by
  intro a
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by simp
    _ = a := by
      rw [add_in_boolean_ring (-a), zero_add]

theorem commutative : ∀ a b : A, a * b = b * a := by
  intro a b
  have : a + b = a * b + b * a + a + b := by calc
    a + b = (a + b) * (a + b) := by rw [BooleanRing.mul_self (a + b)]
    _ = a * a + a * b + b * a + b * b := by
      rw [right_distrib]
      rw [left_distrib, left_distrib]
      exact Eq.symm (add_assoc (a * a + a * b) (b * a) (b * b))
    _ = a + a * b + b * a + b := by
      rw [BooleanRing.mul_self a]
      rw [BooleanRing.mul_self b]
    _ = a * b + b * a + a + b := by
      abel
  have : a * b + b * a = 0 := by
    simp
  rw [add_eq_zero_iff_eq_neg] at this
  rw [neg_eq (b * a)] at this
  exact this
