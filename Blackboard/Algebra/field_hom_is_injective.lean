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
  have : f u * f (u ⁻¹) = 1 := by calc
    f u * f (u ⁻¹) = f (u * u ⁻¹) := by rw [←is_hom.preserve_mul]
    _ = f 1 := by
      refine congrArg f ?_
      rw [CommGroupWithZero.mul_inv_cancel u u_is_not_zero]
    _ = 1 := by rw [←is_hom.preserve_one]

  rw [H] at this
  simp at this

theorem if_fu_is_zero_then_u_must_be_zero'
  (f : F → G) (is_hom : IsFieldHom f)
  : ∀ u : F, f u = 0 → u = 0 := by
  intros u H
  by_contra P
  have := if_u_is_not_zero_then_fu_cannot_be_zero f is_hom u P
  exact this H
theorem if_fu_is_zero_then_u_must_be_zero
  (f : F → G) (is_hom : IsFieldHom f)
  : ∀ u : F, f u = 0 → u = 0 := by
  intros u H
  by_cases u = 0
  case pos P => exact P
  case neg P =>
    have : f u * f (u ⁻¹) = 1 := by calc
      f u * f (u ⁻¹) = f (u * u⁻¹) := by rw [←is_hom.preserve_mul]
      _ = f 1 := by
        refine congr_arg f ?_
        exact CommGroupWithZero.mul_inv_cancel u P
      _ = 1 := by rw [←is_hom.preserve_one]
    rw [H] at this
    simp at this

theorem main
  (f : F → G)
  (is_hom : IsFieldHom f)
  : Function.Injective f := by
  intros x y H
  have : f (x - y) = 0 := by calc
    f (x - y) = f x + f (- y) := by
      rw [←is_hom.preserve_add]
      exact congrArg f (sub_eq_add_neg x y)
    _ = f y + f (- y) := by rw [H]
    _ = f (y + - y) := by rw [is_hom.preserve_add]
    _ = f 0 := by exact congrArg f (add_neg_cancel y)
    _ = 0 := by rw [←is_hom.preserve_zero]

  have : x - y = 0 :=
    if_fu_is_zero_then_u_must_be_zero f is_hom (x - y) this

  rw [sub_eq_iff_eq_add'.mp this]
  simp
