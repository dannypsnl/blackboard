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
  -- 這邊因為構成就是 ij
  -- 1. 根據 j ∈ R 可見 ij ∈ I
  -- 2. 根據 i ∈ R 可見 ij ∈ J
  have L : I * J ≤ I ⊓ J := by exact Ideal.mul_le_inf
  have R : I ⊓ J ≤ I * J := by
    -- r ∈ I 而且 r ∈ J
    intro r ⟨r_in_I, r_in_J⟩
    have : 1 ∈ I + J := (Ideal.eq_top_iff_one (I + J)).mp H
    -- s ∈ I, t ∈ J
    let ⟨s, s_in_I, t, t_in_J, s_add_t_eq_one⟩ :=
      Submodule.mem_sup.mp this
    -- r = r * 1
    rw [←mul_one r]
    -- 1 = s + t 所以 r * 1 = r * (s + t)
    rw [←s_add_t_eq_one]
    -- r * (s + t) = rs + rt
    rw [mul_add r s t]
    -- 證明 rs + rt ∈ I * J 需要證明 rs, rt ∈ I * J
    exact Ideal.add_mem (I * J)
      -- 利用 s ∈ I 跟 r ∈ J 得出相乘 rs ∈ I * J
      (Ideal.mul_mem_mul_rev s_in_I r_in_J)
      -- 利用 r ∈ I 跟 t ∈ J 得出相乘 rt ∈ I * J
      (Ideal.mul_mem_mul r_in_I t_in_J)
  -- 用 anti-symmetry 證明等於
  exact le_antisymm L R
