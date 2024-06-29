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
