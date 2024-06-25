import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Associated
import Mathlib.Algebra.Group.Units

theorem multiply_two_neighbors_is_even
  (n : ℕ)
  : Even (n * (n + 1))
  := by
  have P := Nat.even_or_odd n
  induction P
  . exact Nat.even_mul_succ_self n
  . exact Nat.even_mul_succ_self n

lemma two_is_not_unit : ¬IsUnit 2 := by
  -- idea: proves that 2 is not 1
  intros two_is_unit
  rw [isUnit_iff_eq_one] at two_is_unit
  absurd two_is_unit
  exact Nat.succ_succ_ne_one 0
lemma random_N_is_not_unit (n : ℕ) (H : n ≥ 2) : ¬IsUnit n := by
  -- idea: show that n is not 1
  intros n_is_unit
  rw [isUnit_iff_eq_one] at n_is_unit
  absurd n_is_unit
  exact Nat.ne_of_lt' H

lemma break_lemma
  (n c : ℕ)
  (H : Even n)
  (Q : n > 2)
  (R : n = 2 * c)
  : c ≥ 2
  := by
  have S : n ≥ 4 := by
    -- this one seems indeed hard, how do we know the next even is 4? LOL
    sorry
  rw [R] at S
  have T : 2 * c ≥ 2 * 2 := S
  rw [ge_iff_le] at T
  have M := Nat.le_of_mul_le_mul_left T (Nat.zero_lt_two)
  exact M
theorem any_even_number_except_two_is_not_prime
  (n : ℕ)
  (H : Even n)
  (Q : n > 2)
  : ¬Prime n
  := by
  intros Pn
  have some_m_div_n : ∃ c, n = 2 * c :=
    Even.exists_two_nsmul n H
  have n_is_irreducible := Pn.irreducible
  match some_m_div_n with
    | .intro c div =>
      have isUnit := n_is_irreducible.isUnit_or_isUnit' 2 c div
      induction isUnit
      case inl F => exact two_is_not_unit F
      case inr F =>
        -- idea: Q and H implies n ≥ 4, n = 2 * c, so c must ≥ 2
        have C : c ≥ 2 := break_lemma n c H Q div
        exact random_N_is_not_unit c C F
theorem any_prime_greater_than_two_is_odd
  (p : ℕ)
  (H : Prime p)
  (Q : p > 2)
  : Odd p
  := by
  -- idea:
  -- 1. p : ℕ is even or odd in general, so we do induction
  have I :=  Nat.even_or_odd p
  induction I
  -- 2. but Even side cannot be a prime, by least theorem
  case inl E =>
    have Wow :=
      any_even_number_except_two_is_not_prime p E Q
    absurd Wow H
    exact fun _ ↦ Wow H
  -- 3. so p must be Odd
  case inr O => exact O
