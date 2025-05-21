import Mathlib.Algebra.Ring.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

variable
  [Ring R]

theorem neg_a_mul_neg_b_eq_a_mul_b
  (a b : R)
  : (-a) * (-b) = a * b := by
  rw [neg_mul, mul_neg]
  exact InvolutiveNeg.neg_neg (a * b)

theorem distribute_on_2 (a b : R)
  : 2 * (a * b) = (2 * a) * b
  := by
  simp [two_mul]
  rw [Distrib.right_distrib]

theorem nat_distribute (m : ℕ) (a b : R)
  : AddMonoid.nsmul m (a * b) = (AddMonoid.nsmul m a) * b
  := by
  induction m with
  | zero =>
    rw [AddMonoid.nsmul_zero (a * b)]
    rw [AddMonoid.nsmul_zero a]
    simp
  | succ n P =>
    rw [AddMonoid.nsmul_succ n (a * b)]
    rw [P]
    rw [←Distrib.right_distrib]
    rw [Eq.symm (AddMonoid.nsmul_succ n a)]

theorem int_distribute (m : ℤ) (a b : R)
  : m * (a * b) = (m * a) * b
  := by
  exact Eq.symm (mul_assoc (↑m) a b)

theorem int_distribute'
  (m : ℤ)
  (a b : R)
  : SubNegMonoid.zsmul m (a * b) = (SubNegMonoid.zsmul m a) * b
  := by
  induction m with
  | hz =>
    simp
  | hn =>
    simp
    exact Eq.symm (mul_assoc (-_ - 1) a b)
  | hp =>
    simp
    repeat rw [Distrib.right_distrib]
    simp
    exact Eq.symm (mul_assoc _ a b)

theorem int_distribute''
  (m : ℤ)
  (a b : R)
  : SubNegMonoid.zsmul m (a * b) = (SubNegMonoid.zsmul m a) * b
  := by
  simp
  exact Eq.symm (mul_assoc (↑m) a b)

-- The ring is cyclic under addition means there is a generator `g`
-- any element `x` can be expressed as `ng`
theorem cyclic_on_addition_implies_commutative_ring
  (g : R)
  (H : ∀ x : R, ∃ n : ℕ, x = n • g)
  : ∀ a b : R, a * b = b * a
  := by
  intros a b
  have ⟨m , fact₁⟩ := H a
  have ⟨n, fact₂⟩ := H b
  rw [fact₁, fact₂]
  refine (commute_iff_eq (m • g) (n • g)).mp ?_
  refine Commute.symm (Commute.smul_left ?_ n)
  exact Commute.smul_right rfl m
