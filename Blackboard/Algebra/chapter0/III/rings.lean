import Mathlib.Algebra.Ring.Basic

abbrev IsZeroDivisor [Ring R] (a : R) : Prop :=
  ∃ b ≠ 0, a * b = 0

theorem zero_divisors_in_comm_ring
  [CommRing R]
  (a1 a2 : R)
  (Ha1 : IsZeroDivisor a1)
  (Ha2 : IsZeroDivisor a2)
  (Hb1 : ∀ b : R, Ha1.choose * b = 0 → b = 0)
  : IsZeroDivisor (a1 * a2) := by
  let b1 := Ha1.choose
  let b2 := Ha2.choose
  exists b1 * b2
  have L : b1 * b2 ≠ 0 := by
    refine Ne.intro ?_
    have K : b1 * b2 = 0 → b2 = 0 := Hb1 b2
    intro N
    exact Ha2.choose_spec.left (K N)
  have R := calc
    a1 * a2 * (b1 * b2) = a1 * a2 * b1 * b2 := by
      exact Eq.symm (mul_assoc (a1 * a2) b1 b2)
    _ = a1 * a2 * b1 * b2 := by
      exact rfl
    _ = a1 * b1 * a2 * b2 := by
      exact mul_mul_mul_comm' a1 a2 b1 b2
    _ = (a1 * b1) * (a2 * b2) := by
      exact mul_assoc (a1 * b1) a2 b2
    _ = 0 := by
      rw [Ha1.choose_spec.right]
      exact zero_mul (a2 * b2)
  exact ⟨L, R⟩
