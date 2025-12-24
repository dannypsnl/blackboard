import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Basic

theorem exercise_4_7_to_inv [Group G]
  : ∀ a b : G, (a * b)⁻¹ = a ⁻¹ * b ⁻¹ ↔ a * b = b * a := by
  intros a b
  have IF : (a * b)⁻¹ = a ⁻¹ * b ⁻¹ → a * b = b * a := by
    intro hom
    -- `mul_inv_rev` is not hard to understand
    -- 1. (b * a) * (b * a) ⁻¹ = 1 by definition
    -- 2. b * a * a⁻¹ * b⁻¹ = 1 by cancel law twice
    -- in ONLY_IF we also use this
    have I : (b * a) ⁻¹ = a ⁻¹ * b ⁻¹ := mul_inv_rev b a
    have II : (a * b) ⁻¹ = (b * a) ⁻¹ := Eq.trans hom (Eq.symm I)
    have III : (a * b) ⁻¹ ⁻¹ = (b * a) ⁻¹ ⁻¹ := by
      rw [II]
    have IV : a * b = (a * b) ⁻¹ ⁻¹ := by rw [inv_inv]
    have V : b * a = (b * a) ⁻¹ ⁻¹ := by rw [inv_inv]
    exact Eq.trans IV (Eq.trans III (Eq.symm V))
  have ONLY_IF : a * b = b * a → (a * b)⁻¹ = a ⁻¹ * b ⁻¹ := by
    intro comm
    calc
      (a * b)⁻¹ = (b * a) ⁻¹ := congrArg Inv.inv comm
      _ = a ⁻¹ * b ⁻¹ := mul_inv_rev b a
  exact Iff.intro IF ONLY_IF

local notation x "^2" => x * x
theorem exercise_4_7_to_square [Group G]
  : ∀ a b : G, (a * b)^2 = a^2 * b^2 ↔ a * b = b * a := by
  intros a b
  have IF : (a * b)^2 = a^2 * b^2 → a * b = b * a := by
    intro hom
    rw [mul_assoc, mul_assoc] at hom
    have := (mul_right_inj a (b := b * (a * b))).mp hom
    rw [←mul_assoc, ←mul_assoc] at this
    have := (mul_left_inj b).mp this
    exact Eq.symm this
  have ONLY_IF : a * b = b * a → (a * b)^2 = a^2 * b^2 := by
    intro comm
    calc a * b * (a * b) = a * b * a * b := by exact Eq.symm (mul_assoc (a * b) a b)
         _ = a * (b * a) * b := by
          refine (mul_left_inj b).mpr ?_
          exact mul_assoc a b a
         _ = a * a * b * b := by
          refine (mul_left_inj b).mpr ?_
          rw [mul_assoc]
          refine (mul_right_inj a).mpr ?_
          rw [comm]
         _ = a * a * (b * b) := mul_assoc (a * a) b b
  exact Iff.intro IF ONLY_IF

-- Exercise 6.15
-- This is very general due to Sets behaviour, don't even need to assume they are group homomorphisms
theorem injective_function_is_mono (φ : G → G') (inj : Function.Injective φ)
  : ∀ g1 g2 : K → G, ∀ x, φ (g1 x) = φ (g2 x) → g1 x = g2 x := by
  intros g1 g2 x H
  exact inj H
-- The point is, inverse didn't hold, a monomorphism `f` in Grps is not necessary has a left-inverse (Exercise 6.16)
