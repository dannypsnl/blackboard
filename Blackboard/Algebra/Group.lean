import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Order.Min

-- The understanding way is
-- ∃ n : ℕ, gⁿ = 1
-- and gⁿg⁻ⁿ = 1 since we cancel each by inverse law
-- then we can see 1g⁻ⁿ = g⁻ⁿ = 1
theorem inv_order_eq_order {G : Type u} [Group G]
  (g : G) : orderOf g⁻¹ = orderOf g
  := by simp

theorem aabb {G : Type u} [Group G]
  (a b : G)
  : (a * b) ^ 2 = a ^ 2 * b ^ 2 ↔ a * b = b * a
  := by
  simp [sq]
  refine Iff.intro ?a ?b
  case a =>
    intros ab
    rw [mul_assoc, mul_assoc, ←mul_assoc b a b, ←mul_assoc a b b] at ab
    rw [mul_left_cancel_iff] at ab
    rw [mul_right_cancel_iff] at ab
    exact id (Eq.symm ab)
  case b =>
    intros comm
    rw [←mul_assoc, ←mul_assoc, mul_assoc a b a]
    rw [←comm]
    simp [mul_assoc]

theorem inv_of_prod {G : Type u} [Group G]
  : ∀ a b : G, (a * b)⁻¹ = b⁻¹ * a⁻¹
  := by simp

theorem comm_inv_of_prod {G : Type u} [CommGroup G]
  : ∀ a b : G, a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹
  := by
  intros a b
  rw [←inv_of_prod a b, ←inv_of_prod b a, mul_comm]

theorem pow2_is_1_implies_commute {G : Type u} [Group G]
  (P : ∀ a : G, a * a = 1)
  : ∀ a b : G, Commute a b
  := by
  intros a b
  refine (commute_iff_eq a b).mpr ?_
  have fact2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    simp [sq]
    rw [P (a * b), P a, P b]
    exact Eq.symm (LeftCancelMonoid.one_mul 1)
  exact (aabb a b).mp fact2
