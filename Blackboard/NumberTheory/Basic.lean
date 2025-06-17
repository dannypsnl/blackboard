import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Prime.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Basic

theorem multiply_two_neighbors_is_even
  (n : ℕ)
  : Even (n * (n + 1))
  := by
  induction n.even_or_odd
  · exact Nat.even_mul_succ_self n
  · exact Nat.even_mul_succ_self n

lemma break_lemma
  (n c : ℕ)
  (is_even : Even n)
  (greater_than_two : n > 2)
  (equation : n = 2 * c)
  : c ≥ 2
  := by
  -- idea:
  -- 1. 3 is not even, so n ≠ 3
  have three_is_not_even : ¬Even 3 := Nat.not_even_two_mul_add_one 1
  have n_ne_3 : n ≠ 3 := by
    intros n_eq_three
    rw [n_eq_three] at is_even
    exact three_is_not_even is_even
  have B : n > 3 := by
    exact Nat.lt_of_le_of_ne greater_than_two (id (Ne.symm n_ne_3))
  -- 2. 4 is even
  -- this one seems indeed hard, how do we know the next even is 4? LOL
  have n_ge_4 : n ≥ 4 := by
    exact B
  rw [equation] at n_ge_4
  have T : 2 * c ≥ 2 * 2 := n_ge_4
  rw [ge_iff_le] at T
  have M := Nat.le_of_mul_le_mul_left T (Nat.zero_lt_two)
  exact M
theorem even_numbers_except_two_is_not_prime
  (n : ℕ)
  (is_even : Even n)
  (greater_than_two : n > 2)
  : ¬Nat.Prime n
  := by
  intros is_prime
  have some_m_div_n : ∃ c, n = 2 * c :=
    is_even.exists_two_nsmul n
  obtain ⟨c, Dvd⟩ := some_m_div_n
  have ha : 2 ≠ 1 := Nat.succ_succ_ne_one 0
  have hb : c ≠ 1 := by
    refine Nat.ne_of_lt' ?_
    exact break_lemma n c is_even greater_than_two Dvd
  have C := Nat.not_prime_mul' (a := 2) (b := c) Dvd.symm ha hb
  exact C is_prime

theorem all_primes_greater_than_two_is_odd
  (p : ℕ)
  (is_prime : Nat.Prime p)
  (greater_than_two : p > 2)
  : Odd p
  := by
  -- idea:
  -- 1. p : ℕ is even or odd in general, so we do induction
  induction p.even_or_odd with
  -- 2. but Even side cannot be a prime, by least theorem
  | inl E =>
    have thm :=
      even_numbers_except_two_is_not_prime p E greater_than_two
    absurd thm is_prime
    exact fun _ ↦ thm is_prime
  -- 3. so p must be Odd
  | inr O => exact O

lemma the_form_is_odd (n : ℕ) (the_form : n = 4 * k + 3)
  : Odd n
  := by
  have is_even_4 : Even 4 := Nat.even_iff.mpr rfl
  have is_even_4_times_k : Even (4 * k) := is_even_4.mul_right k
  have is_odd_3 : Odd 3 := Nat.odd_iff.mpr rfl
  have n_is_odd : Odd (4 * k + 3) := is_even_4_times_k.add_odd is_odd_3
  rw [←the_form] at n_is_odd
  exact n_is_odd

lemma two_cannot_be_prod_of_four (n : ℕ) : ¬ 2 = 4 * n := by
  induction n with
  | zero =>
    exact Nat.ne_of_beq_eq_false rfl
  | succ n P =>
    exact Nat.ne_of_beq_eq_false rfl
lemma the_dvd_cannot_hold (k : ℕ) : ¬ (4 ∣ 4 * k + 2) := by
  intros F
  induction exists_eq_mul_right_of_dvd F with
  | intro c P =>
  have guess2 : 2 = 4 * c - 4 * k := by
    exact Nat.eq_sub_of_add_eq' P
  simp [mul_comm, ←Nat.sub_mul] at guess2
  rw [←mul_comm 4] at guess2
  exact (two_cannot_be_prod_of_four (c-k)) guess2
lemma even_odd_case
  (n k a b : ℕ)
  (the_form : n = 4 * k + 3)
  (a_is_even : ∃ k, a = 2 * k)
  (b_is_odd : ∃ k, b = 2 * k + 1)
  : ¬ (n = a * a + b * b)
  := by
  intros negation
  induction a_is_even with
  | intro c a_as_c =>
  induction b_is_odd with
  | intro d b_as_d =>
  rw [a_as_c, b_as_d] at negation
  -- rewrite to 4 * c * c
  simp [mul_assoc, ←mul_assoc c 2 c, mul_comm c 2, ←mul_assoc 2 2 (c * c)] at negation
  -- rewrite to 4 * d * d + 4 * d + 1
  simp [RightDistribClass.right_distrib, LeftDistribClass.left_distrib] at negation
  simp [mul_assoc, ←mul_assoc d 2 d, mul_comm d 2, ←mul_assoc 2 2 (d * d)] at negation
  rw [add_assoc] at negation
  rw [←add_assoc (2*d) (2*d) 1] at negation
  simp [←RightDistribClass.right_distrib] at negation
  rw [←add_assoc, ←add_assoc] at negation
  -- rewrite to (...) * 4 + 1
  simp [mul_comm 4, ←distrib_three_right] at negation
  rw [mul_comm] at negation
  rw [negation] at the_form
  have target : 4 * (c * c + d * d + d) = 4 * k + 2 := by
    exact Eq.symm ((fun {a b} ↦ Nat.succ_inj.mp) (id (Eq.symm the_form)))
  have should_dvd := target.dvd
  have should_dvd_four : 4 ∣ 4 * k + 2 := by
    exact dvd_of_mul_right_dvd should_dvd
  have contra := the_dvd_cannot_hold k
  exact contra should_dvd_four

theorem n_with_form_cannot_be_perfect_square
  (n k : ℕ)
  (the_form : n = 4 * k + 3)
  : ¬ (∃ a b : ℕ, n = a * a + b * b)
  := by
  intros hypothesis
  have n_is_odd := the_form_is_odd n the_form
  induction hypothesis with
  | intro a P =>
  induction P with
  | intro b new_form =>
  induction a.even_or_odd with
  | inl aE =>
    induction b.even_or_odd with
    | inl bE =>
      have n_is_even := Even.add (aE.mul_left a) (bE.mul_left b)
      rw [←new_form] at n_is_even
      have not_even := Nat.not_even_iff_odd.mpr n_is_odd
      exact not_even n_is_even
    | inr bO =>
      have l : ¬ (n = a * a + b * b) := even_odd_case n k a b the_form (aE.exists_two_nsmul a) bO
      exact l new_form
  | inr aO =>
    induction b.even_or_odd with
    | inl bE =>
      have l : ¬ (n = b * b + a * a) := even_odd_case n k b a the_form (bE.exists_two_nsmul b) aO
      rw [add_comm] at new_form
      exact l new_form
    | inr bO =>
      have n_is_even := (aO.mul aO).add_odd (bO.mul bO)
      have n_is_not_odd := Nat.not_odd_iff_even.mpr n_is_even
      rw [←new_form] at n_is_not_odd
      exact n_is_not_odd n_is_odd
