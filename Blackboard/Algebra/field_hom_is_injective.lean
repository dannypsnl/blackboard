import Mathlib.Algebra.Field.Basic

variable
  [Field F] [Field G]

class IsFieldHom (f : F → G) : Prop where
  preserve_add : f (a + b) = f a + f b
  preserve_mul : f (a * b) = f a * f b
  preserve_one : f 1 = 1
  preserve_zero : f 0 = 0

theorem if_u_is_not_zero_then_fu_cannot_be_zero
  (f : F → G) (is_hom : IsFieldHom f)
  : ∀u ≠ 0, f u ≠ 0 := by
  intros u u_is_not_zero
  by_contra H
  have : f u * f (u ⁻¹) = 1 := by
    rw [←is_hom.preserve_one]
    rw [←is_hom.preserve_mul]
    refine congrArg f ?_
    rw [CommGroupWithZero.mul_inv_cancel u u_is_not_zero]
  rw [H] at this
  simp at this
