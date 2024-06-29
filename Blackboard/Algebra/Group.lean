import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Order.Min

variable
  (G : Type u)
  [Group G]

-- The understanding way is
-- ∃ n : ℕ, gⁿ = 1
-- and gⁿg⁻ⁿ = 1 since we cancel each by inverse law
-- then we can see 1g⁻ⁿ = g⁻ⁿ = 1
theorem inv_order_eq_order (g : G) : orderOf g⁻¹ = orderOf g
  := by simp

theorem aabb
  (a b : G)
  : (a * b) ^ 2 = a ^ 2 * b ^ 2 ↔ a * b = b * a
  := by
  refine Iff.intro ?a ?b
  simp [sq]
  case a =>
    intros ab
    rw [mul_assoc, mul_assoc, ←mul_assoc b a b, ←mul_assoc a b b] at ab
    rw [mul_left_cancel_iff] at ab
    rw [mul_right_cancel_iff] at ab
    exact id (Eq.symm ab)
  case b =>
    simp [sq]
    intros comm
    rw [←mul_assoc, ←mul_assoc, mul_assoc a b a]
    rw [←comm]
    simp [mul_assoc]
