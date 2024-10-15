import Mathlib.Analysis.SpecialFunctions.Integrals

theorem const_mul
  {a : ℝ} {b : ℝ}
  {f : ℝ → ℝ}
  : ∫ (x : ℝ) in a..b, c * f x = c * ∫ (x : ℝ) in a..b, f x
  := by
  exact intervalIntegral.integral_const_mul c f
