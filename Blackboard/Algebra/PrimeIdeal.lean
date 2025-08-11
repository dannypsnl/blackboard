import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

variable [CommRing R]

class Ideal.IsPrime (I : Ideal R) : Prop where
  property (a b : R) : a * b ∈ I → a ∈ I ∨ b ∈ I

open Ideal.Quotient

lemma backward
  (I : Ideal R)
  [I.IsTwoSided]
  [nzd : NoZeroDivisors (R ⧸ I)]
  : I.IsPrime := {
    property a b P := by
      have : ((mk I) a) * ((mk I) b) = (mk I) 0 → ((mk I) a) = (mk I) 0 ∨ ((mk I) b) =  (mk I) 0 := by
        exact nzd.eq_zero_or_eq_zero_of_mul_eq_zero
      have zero : (mk I) 0 = 0 := rfl
      rw [zero] at this
      have something : (mk I) a * (mk I) b = (mk I) (a * b) := rfl
      rw [something] at this
      repeat rw [eq_zero_iff_mem] at this
      exact this P
  }

lemma forward
  (I : Ideal R)
  [I.IsTwoSided]
  [prime : I.IsPrime]
  : NoZeroDivisors (R ⧸ I) := {
    eq_zero_or_eq_zero_of_mul_eq_zero := by
      intros a b P
      rw [←mk_out a, ←mk_out b]
      repeat rw [eq_zero_iff_mem]

      rw [←mk_out a] at P
      rw [←mk_out b] at P
      have R : mk I (Quotient.out a) * mk I (Quotient.out b) = mk I (Quotient.out a * Quotient.out b) := rfl
      rw [R] at P
      rw [eq_zero_iff_mem] at P

      exact prime.property (Quotient.out a) (Quotient.out b) P
  }

theorem ideal_is_prime_iff_quotient_is_integral_domain
  (I : Ideal R)
  [I.IsTwoSided]
  : I.IsPrime ↔ NoZeroDivisors (R ⧸ I) := {
    mp _prime := forward I
    mpr _nzd := backward I
  }
