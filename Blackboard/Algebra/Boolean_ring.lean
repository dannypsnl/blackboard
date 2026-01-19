import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

variable [BooleanRing A]

theorem add_in_boolean_ring
  : ∀ a : A, a + a = 0 := by
  intro a
  have := by calc
    a + a = (a + a) * (a + a) := by rw [BooleanRing.mul_self (a + a)]
    _ = a * a + a * a + a * a + a * a := by
      rw [right_distrib]
      rw [left_distrib]
      exact Eq.symm (add_rotate (a * a + a * a) (a * a) (a * a))
    _ = a + a + a + a := by rw [BooleanRing.mul_self a]
  simp at this
  exact this

lemma neg_eq : ∀ a : A, -a = a := by
  intro a
  calc
    -a = -a + 0 := by rw [add_zero]
    _ = -a + -a + a := by simp
    _ = a := by
      rw [add_in_boolean_ring (-a), zero_add]

-- Boolean ring is commutative
theorem commutative : ∀ a b : A, a * b = b * a := by
  intro a b
  have : a + b = a + b + (a * b + b * a) := by calc
    a + b = (a + b) * (a + b) := by rw [BooleanRing.mul_self (a + b)]
    _ = a * a + a * b + b * a + b * b := by
      rw [right_distrib]
      rw [left_distrib, left_distrib]
      exact Eq.symm (add_assoc (a * a + a * b) (b * a) (b * b))
    _ = a + a * b + b * a + b := by
      rw [BooleanRing.mul_self a]
      rw [BooleanRing.mul_self b]
    _ = a + b + (a * b + b * a) := by
      abel
  have : a * b + b * a = 0 := by
    rw [left_eq_add] at this
    exact this
  rw [add_eq_zero_iff_eq_neg] at this
  rw [neg_eq (b * a)] at this
  exact this

-- A is Boolean ring + integral domain, then the only elements of A are 0 and 1
theorem has_only_two_elements [IsDomain A] : ∀ a : A, a = 0 ∨ a = 1 := by
  intro a
  -- From a * a = a, we get a * (a - 1) = 0
  have h : a * (a - 1) = 0 := by
    calc a * (a - 1) = a * a - a * 1 := by ring
    _ = a - a := by rw [BooleanRing.mul_self a, mul_one]
    _ = 0 := by ring
  -- In an integral domain, this means a = 0 or a - 1 = 0
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with ha | ha1
  · left; exact ha
  · right
    rw [sub_eq_zero] at ha1
    exact ha1

open Ideal.Quotient
-- A a Boolean ring, then A/I is a Boolean ring
instance quotient_boolean_ring (I : Ideal A) : BooleanRing (A ⧸ I) where
  isIdempotentElem := fun i => by
    obtain ⟨a, rfl⟩ := mk_surjective i
    show mk I a * mk I a = mk I a
    calc
      mk I a * mk I a = mk I (a * a) := by
        rw [←map_mul]
      _ = mk I a := by
        rw [BooleanRing.mul_self]

-- A a Boolean ring, then we have
-- 1. A/I is a Boolean ring
-- 2. I is prime => A/I is domain
-- 1 + 2 => A/I is F2
theorem every_quotient_of_prime_ideals_is_F2
  (I : Ideal A) [hP : I.IsPrime]
  : ∀ a : (A ⧸ I), a = 0 ∨ a = 1 := by
  haveI : IsDomain (A ⧸ I) := isDomain I
  exact has_only_two_elements

-- Every prime ideal of a Boolean ring is a maximal ideal
theorem prime_implies_maximal (I : Ideal A) [hP : I.IsPrime] : I.IsMaximal := by
  -- Show I is maximal using the characterization
  rw [Ideal.isMaximal_iff]
  constructor
  case left =>
    -- because I is prime I ≠ A, hence 1 ∉ I
    exact I.ne_top_iff_one.mp hP.ne_top
  case right =>
    -- For any J ⊇ I and x ∉ I with x ∈ J, show 1 ∈ J (i.e. J = A)
    intro J x I_le_J x_not_in_I x_in_J
    -- Because A/I is Boolean + integral domain, hence every element is 0 or 1.
    rcases every_quotient_of_prime_ideals_is_F2 I (mk I x) with hZ | hO
    case inl =>
      -- x ∈ I ↔ mk x = 0 ∈ A/I
      -- In A/I ∋ mk x ≠ 0 (because x ∉ I)
      have mkX_ne_zero : mk I x ≠ 0 := by
        rw [ne_eq, eq_zero_iff_mem]
        exact x_not_in_I
      exact absurd hZ mkX_ne_zero
    case inr =>
      have x_in_I : (1 : A) - x ∈ I := by
        rw [←eq_zero_iff_mem]
        calc
          mk I (1 - x) = mk I 1 - mk I x := by rw [map_sub]
          _ = 1 - mk I x := by rw [map_one]
          _ = 1 - 1 := by rw [hO]
          _ = 0 := by rw [sub_self]
      have h1x_in_J : (1 : A) - x ∈ J := I_le_J x_in_I
      -- Because x ∈ J and 1 - x ∈ J, we have 1 = x + (1 - x) ∈ J
      have one_in_J : x + (1 - x) ∈ J := J.add_mem x_in_J h1x_in_J
      rw [add_sub_cancel] at one_in_J
      exact one_in_J
