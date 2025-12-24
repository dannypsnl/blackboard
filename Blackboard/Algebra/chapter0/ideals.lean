import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations

lemma contain_zero [Ring R] (I : Ideal R) : 0 ∈ I := Submodule.zero_mem I

lemma contain_one_means_what? [Ring R] (I : Ideal R)
  (one_in_I : 1 ∈ I)
  : ∀ r : R, r ∈ I := by
  intro r
  rw [←mul_one r]
  exact Ideal.mul_mem_left I r one_in_I

theorem exercise_4_5
  [CommRing R]
  (I J : Ideal R)
  (H : I + J = ⊤)
  : I * J = I ⊓ J := by
  have : I + J = I ⊔ J := Ideal.add_eq_sup
  have : IsCoprime I J := by
    rw [this] at H
    exact Ideal.isCoprime_iff_sup_eq.mpr H
  rw [Ideal.inf_eq_mul_of_isCoprime this]
