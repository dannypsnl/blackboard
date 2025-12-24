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
  have L : I * J ≤ I ⊓ J := by exact Ideal.mul_le_inf
  have R : I ⊓ J ≤ I * J := by
    intro r ⟨r_in_I, r_in_J⟩
    let ⟨s, s_in_I, t, t_in_J, s_add_t_eq_one⟩ :=
      Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 H)
    rw [←mul_one r]
    rw [←s_add_t_eq_one]
    rw [mul_add r s t]
    exact Ideal.add_mem (I * J)
      (Ideal.mul_mem_mul_rev s_in_I r_in_J)
      (Ideal.mul_mem_mul r_in_I t_in_J)
  exact le_antisymm L R
