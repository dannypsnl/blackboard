import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Basic

-- Exercise 6.15
-- This is very general due to Sets behaviour, don't even need to assume they are group homomorphisms
theorem injective_function_is_mono (φ : G → G') (inj : Function.Injective φ)
  : ∀ g1 g2 : K → G, ∀ x, φ (g1 x) = φ (g2 x) → g1 x = g2 x := by
  intros g1 g2 x H
  exact inj H
