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
