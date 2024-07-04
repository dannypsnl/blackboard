import Mathlib.Algebra.Ring.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

theorem distribute_on_2 {R : Type u} [Ring R]
  (a b : R)
  : 2 * (a * b) = (2 * a) * b
  := by
  simp [two_mul]
  rw [Distrib.right_distrib]

theorem nat_distribute {R : Type u} [Ring R]
  (m : ℕ)
  (a b : R)
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

theorem int_distribute {R : Type u} [Ring R]
  (m : ℤ)
  (a b : R)
  : m * (a * b) = (m * a) * b
  := by
  exact Eq.symm (mul_assoc (↑m) a b)

theorem int_distribute' {R : Type u} [Ring R]
  (m : ℤ)
  (a b : R)
  : SubNegMonoid.zsmul m (a * b) = (SubNegMonoid.zsmul m a) * b
  := by
  induction m with
  | ofNat n =>
    simp
    exact Eq.symm (mul_assoc (↑n) a b)
  | negSucc n =>
    simp
    repeat rw [Distrib.right_distrib]
    simp
    exact Eq.symm (mul_assoc (↑n) a b)

theorem int_distribute'' {R : Type u} [Ring R]
  (m : ℤ)
  (a b : R)
  : SubNegMonoid.zsmul m (a * b) = (SubNegMonoid.zsmul m a) * b
  := by
  simp
  exact Eq.symm (mul_assoc (↑m) a b)

theorem cyclic_on_addition_implies_commutative_ring {R : Type u} [Ring R]
  -- The ring is cyclic under addition means there is a generator `g`
  -- any element `x` can be expressed as `ng`
  (g : R)
  (H : ∀ x : R, ∃ n : ℕ, x = n • g)
  : ∀ a b : R, a * b = b * a
  := by
  intros a b
  have ⟨m , fact₁⟩ := H a
  have ⟨n, fact₂⟩ := H b
  rw [fact₁, fact₂]
  repeat rw [Distrib.right_distrib]
  rw [smul_mul_smul m n]
  rw [smul_mul_smul n m]
  rw [Nat.mul_comm]
