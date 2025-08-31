open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

-- https://mathstodon.xyz/@MartinEscardo/111410774463719132
module escardo-0002 where

variable
  ℓ : Level
  P : Type ℓ

𝟚 = Bool

middle : (isProp P) → P ⊎ (P → ⊥) → 𝟚
middle is-Prop (inl x) = true
middle is-Prop (inr x) = false
