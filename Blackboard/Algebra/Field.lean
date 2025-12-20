import Mathlib.Algebra.Field.Defs

theorem Each_field_is_an_integral_domain
  [Field K]
  : NoZeroDivisors K := {
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intros a b P
    refine or_iff_not_imp_left.mpr ?_
    intro a_ne_zero
    have H : a * b * (1 / a) = 0 * (1 / a) := by
      exact congrFun (congrArg HMul.hMul P) (1 / a)
    have H2 : a * b * (1 / a) = b := by
      rw [mul_comm, ←mul_assoc, mul_comm _ a]
      simp
      rw [DivisionRing.mul_inv_cancel a a_ne_zero]
      exact one_mul b
    rw [←H2, H]
    simp
  }
