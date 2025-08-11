import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs

variable [CommRing R]

class Ideal.IsPrime (I : Ideal R) : Prop where
  property (a b : R) : a * b ∈ I → a ∈ I ∨ b ∈ I

open Ideal.Quotient

theorem quotient_is_integral_domain_implies_the_ideal_is_prime
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
