import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory
open SimplexCategory

theorem my_δ_comp_δ
  {n : ℕ}
  {i j : Fin (n + 2)}
  (H : i ≤ j) :
  (δ i) ≫ (δ j.succ) = (δ j) ≫ (δ i.castSucc) := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> . simp at * <;> omega
