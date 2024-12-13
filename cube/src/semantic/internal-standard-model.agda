module semantic.internal-standard-model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

record M {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    Ty⋄ : Type ℓ
    Tm⋄ : Ty⋄ → Type ℓ
    Σ⋄ : (A : Ty⋄) → (Tm⋄ A → Ty⋄) → Ty⋄

  Con : Type ℓ
  Con = Ty⋄

  Ty : Con → Type ℓ
  Ty Γ = Tm⋄ Γ → Ty⋄

  -- Tm : Con → Ty → Type
  -- Tm Γ A = (γ : Tm⋄ Γ) → Tm⋄ (A γ)

  -- _▹_ : Con → Ty → Con
  -- Γ ▹ A = Σ⋄ Γ A
 