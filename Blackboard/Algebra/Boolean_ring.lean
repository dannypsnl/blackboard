import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

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
  have : a + b = a + b + (a * b + b * a) := by calc
    a + b = (a + b) * (a + b) := by rw [BooleanRing.mul_self (a + b)]
    _ = a * a + a * b + b * a + b * b := by
      rw [right_distrib]
      rw [left_distrib, left_distrib]
      exact Eq.symm (add_assoc (a * a + a * b) (b * a) (b * b))
    _ = a + a * b + b * a + b := by
      rw [BooleanRing.mul_self a]
      rw [BooleanRing.mul_self b]
    _ = a + b + (a * b + b * a) := by
      abel
  have : a * b + b * a = 0 := by
    rw [eq_comm] at this
    have Z := add_zero (a + b)
    have := Eq.trans this (Eq.symm Z)
    have := add_left_cancel (a := a + b) (b := a * b + b * a) (c := 0) this
    exact this
  rw [add_eq_zero_iff_eq_neg] at this
  rw [neg_eq (b * a)] at this
  exact this

-- In a Boolean ring that is also an integral domain,
-- the only elements are 0 and 1
theorem has_only_two_elements [IsDomain A] : ∀ a : A, a = 0 ∨ a = 1 := by
  intro a
  -- From a * a = a, we get a * (a - 1) = 0
  have h : a * (a - 1) = 0 := by
    calc a * (a - 1) = a * a - a * 1 := by ring
    _ = a - a := by rw [BooleanRing.mul_self a, mul_one]
    _ = 0 := by ring
  -- In an integral domain, this means a = 0 or a - 1 = 0
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with ha | ha1
  · left; exact ha
  · right
    rw [sub_eq_zero] at ha1
    exact ha1
