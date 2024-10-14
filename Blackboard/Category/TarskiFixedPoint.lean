import Mathlib.Order.Defs
import Mathlib.Order.CompleteLattice

variable
  {P : Type u₁} [CompleteLattice P]

def equiv (a b : P) : Prop :=
  a ≤ b ∧ b ≤ a
notation a " ≈ " b => equiv a b


def Tarski (h : P → P)
  (H : Monotone h)
  : ∃ y : P, h y ≈ y
  := by
  let Carry := { z : P | z ≤ h z }
  let y : P := sSup Carry
  have l₂ : y ≤ h y := by
    rw [sSup_le_iff]
    intros b b_in
    have b_le_y := le_sSup b_in
    exact Preorder.le_trans b (h b) (h y) b_in (H b_le_y)
  have l₁ : h y ≤ y := CompleteLattice.le_sSup Carry (h y) (H l₂)
  exact ⟨ y , ⟨ l₁ , l₂ ⟩ ⟩
