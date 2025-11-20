import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

def SeqLim (a : ℕ → ℝ) (L : ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε
def SeqConv (a : ℕ → ℝ): Prop := ∃L, SeqLim a L

theorem ArchProp (_: 0 < (ε : ℝ)) : ∃ (N : ℕ), 1 / ε < ↑N := by
  have fact : 1 / ε ≤ ⌈1 / ε⌉₊ := by bound
  use ⌈1 / ε⌉₊ + 1
  push_cast
  bound

theorem an_coverges_to_zero
  (a: ℕ → ℝ)
  (ha: ∀ (n : ℕ), a n = 1 / ↑n)
  : SeqLim a 0
  := by
  change ∀ ε > 0 , ∃ N , ∀ n ≥ N , |a n - 0| < ε
  intro ε hε
  have f1 : ∃ ( N : ℕ ) , 1 / ε < N := by apply ArchProp hε
  choose N eps_inv_lt_N using f1
  use N
  intro n n_ge_N
  ring_nf
  specialize ha n
  rewrite [ ha ]
  have f2 : |1 / (n : ℝ )| = 1 / n := by bound
  rewrite [ f2 ]
  have f3 : 0 < 1 / ε := by bound
  have Npos : (0 : ℝ) < N := by linarith [f3 , eps_inv_lt_N]
  have N_le_n : ( N : ℝ) ≤ n := by exact_mod_cast n_ge_N
  have npos : (0 : ℝ) < n := by linarith [Npos , N_le_n]
  field_simp
  field_simp at eps_inv_lt_N
  have f4 : N * ε ≤ n * ε := by bound
  linarith [eps_inv_lt_N, f4]

theorem an_diverges
  (a : ℕ → ℝ)
  (ha: ∀ (n : ℕ), a n = (-1) ^ n)
  : ¬SeqConv a := by
  change SeqConv a →False
  intro H
  choose L hL using H
  have := hL (1/2) one_half_pos
  choose N hN using this

  have fact : |((-1)^N - L) + -((-1)^(N+1) - L)| ≤ |((-1)^N - L)| + |-((-1)^(N+1) - L)| := by apply abs_add_le
  have final : |((-1)^N - L) + -((-1)^(N+1) - L)| < 1 := by
    have : |((-1)^N - L)| + |(-1)^(N+1) - L| = |((-1)^N - L)| + |-((-1)^(N+1) - L)| := by
      refine (add_right_inj |(-1) ^ N - L|).mpr ?_
      exact Eq.symm (abs_neg ((-1) ^ (N + 1) - L))
    rewrite [Eq.symm this] at fact
    have left := hN N (by exact Nat.le_refl N)
    have right := hN (N+1) (Nat.le_add_right N 1)
    rw [ha N] at left
    rw [ha (N+1)] at right
    have := lt_of_le_of_lt fact (add_lt_add left right)
    ring_nf at this
    ring_nf
    exact this
  have : (-1 : ℝ)^(N+1) = -1 * ((-1)^N) := by
    exact pow_succ' (-1) N
  rewrite [this] at final
  ring_nf at final

  induction N.even_or_odd
  case inl isEven =>
    have : (-1)^N = (1 : ℝ) := Even.neg_one_pow isEven
    rewrite [this] at final
    ring_nf at final
    exact absurd final (by exact Nat.not_ofNat_lt_one)
  case inr isOdd =>
    have : (-1)^N = (-1 : ℝ) := Odd.neg_one_pow isOdd
    rewrite [this] at final
    ring_nf at final
    exact absurd final (by exact Nat.not_ofNat_lt_one)

theorem scale (a b : ℕ → ℝ)
  (h : SeqLim a L) -- a 收斂到 L
  (b_scaled : ∀ n , b n = 2 * a n) -- b 等於 2a
  -- 證明 b 收斂到 2L
  : SeqLim b (2 * L) := by
  change ∀ ε > 0 , ∃ N , ∀ n ≥ N , |b n - 2*L| < ε
  intro ε hε

  change ∀ ε1 > 0 , ∃ N1 , ∀ n ≥ N1 , |a n - L| < ε1 at h
  have eps_half_pos : 0 < ε / 2 := by bound
  specialize h (ε / 2) eps_half_pos
  choose N hN using h

  use N
  intro n hn
  specialize b_scaled n
  have factor : 2 * a n - 2 * L = 2 * (a n - L) := by ring_nf
  rw [b_scaled, factor]
  rw [abs_mul]
  specialize hN n hn
  norm_num
  linarith
