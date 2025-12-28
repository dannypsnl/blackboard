import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations

variable
  [CommRing R]

theorem exercise_0_4
  (I J K : Ideal R)
  : I * (J + K) = I * J + I * K := by
  rw [add_eq_sup, add_eq_sup]
  exact Ideal.mul_sup I J K

notation "√" I => Ideal.radical I

theorem proposition_0_8_I (I : Ideal R)
  : I ≤ √ I := by
  intro i ih
  refine Ideal.mem_radical_iff.mpr ?_
  exists 1
  exact (pow_one i).symm ▸ ih

lemma ideal_order {I J K : Ideal R} : I ≤ J → J ≤ K → I ≤ K :=
  fun p q ⦃_⦄ i ↦ q (p i)

theorem proposition_0_8_II (I : Ideal R)
  : (√ I) = √ √ I := by
  have L : (√ I) ≤ √ √ I := proposition_0_8_I (√ I)
  have R : (√ √ I) ≤ √ I := by
    intros i ih
    -- 1. unroll `i ∈ √√I`
    have f : ∃ n, i ^ n ∈ √ I := Ideal.mem_radical_iff.mp ih
    -- 2. unroll `i^n ∈ √I` nested in `∃`
    have s : ∃ n, (i ^ f.choose) ^ n ∈ I := Ideal.mem_radical_iff.mp f.choose_spec
    refine Ideal.mem_radical_iff.mpr ?_
    -- choose `n * m`
    exists f.choose * s.choose
    -- rewrite i^(n * m) to (i^n)^m
    rw [pow_mul]
    -- and that's exactly the second unroll
    have : (i ^ f.choose) ^ s.choose ∈ I := s.choose_spec
    exact this
  exact le_antisymm L R
