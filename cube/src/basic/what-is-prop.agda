open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty

module basic.what-is-prop where

variable
  ℓ : Level

⊥-is-prop : isProp ⊥
⊥-is-prop = λ ()

prop→⊥-is-prop : (P : Type ℓ) → isProp P → isProp (P → ⊥)
prop→⊥-is-prop P P-is-prop = isPropΠ (λ x ())

set-equation₁ : {X : Type ℓ} → isSet X → (x y : X) → isProp (x ≡ y → ⊥)
set-equation₁ is-set x y = prop→⊥-is-prop (x ≡ y) (is-set x y)

set-equation₂ : {X : Type ℓ} → isSet X → (x y : X) → isProp ((x ≡ y → ⊥) → ⊥)
set-equation₂ is-set x y = prop→⊥-is-prop (x ≡ y → ⊥) (set-equation₁ is-set x y)
