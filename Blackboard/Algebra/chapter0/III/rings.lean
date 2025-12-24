import Mathlib.Algebra.Ring.Basic

abbrev IsZeroDivisor [Ring R] (a : R) : Prop :=
  ∃ b : R, a * b = 0

theorem zero_divisors_in_comm_ring
  [CommRing R]
  (a1 a2 : R)
  : IsZeroDivisor a1 ∧ IsZeroDivisor a2 → IsZeroDivisor (a1 * a2) := by
  intro ⟨Ha1 , Ha2⟩
  let b1 := Ha1.choose
  let b2 := Ha2.choose
  exists b1 * b2
  calc
    a1 * a2 * (b1 * b2) = a1 * a2 * b1 * b2 := by
      exact Eq.symm (mul_assoc (a1 * a2) b1 b2)
    _ = a1 * a2 * b1 * b2 := by
      exact rfl
    _ = a1 * b1 * a2 * b2 := by
      exact mul_mul_mul_comm' a1 a2 b1 b2
    _ = (a1 * b1) * (a2 * b2) := by
      exact mul_assoc (a1 * b1) a2 b2
    _ = 0 := by
      rw [Ha1.choose_spec]
      exact zero_mul (a2 * b2)
