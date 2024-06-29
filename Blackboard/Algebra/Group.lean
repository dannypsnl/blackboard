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
  apply Iff.intro
  case mp =>
    intros ab
    rw [mul_assoc, mul_assoc, ←mul_assoc b a b, ←mul_assoc a b b] at ab
    rw [mul_left_cancel_iff] at ab
    rw [mul_right_cancel_iff] at ab
    exact id (Eq.symm ab)
  case mpr =>
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
  apply (commute_iff_eq a b).mpr
  have fact2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
    simp [sq]
    rw [P (a * b), P a, P b]
    exact Eq.symm (LeftCancelMonoid.one_mul 1)
  exact (aabb a b).mp fact2

theorem inf_order_inequality {G : Type u} [Group G]
  (a : G)
  (P : ¬IsOfFinOrder a)
  -- although I use n < m here, but that's just to ignore inequality cases, it holds for all n ≠ m in ℕ.
  (Q : n < m)
  : a ^ m ≠ a ^ n
  := by
  rw [←orderOf_eq_zero_iff] at P
  rw [orderOf_eq_zero_iff'] at P
  have P' := P (m - n) (Nat.zero_lt_sub_of_lt Q)
  rw [pow_sub] at P'
  case h => exact Nat.le_of_succ_le Q
  intro Ne
  have F : a ^ m * (a ^ n)⁻¹ = 1 := by
    refine Eq.symm (eq_mul_inv_of_mul_eq ?h)
    simp
    exact id (Eq.symm Ne)
  exact P' F
