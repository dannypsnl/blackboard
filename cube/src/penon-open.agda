open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Empty using (⊥) renaming (rec to byAbsurdity)

module penon-open where

ℙ : {ℓ : Level} → (X : Type ℓ) → Type (ℓ-suc ℓ)
ℙ {ℓ} X = X → Type ℓ

_∈_ : {ℓ : Level} → {X : Type ℓ} → (x : X) → (U : ℙ X) → Type ℓ
x ∈ U = U x

_⊂_ : {ℓ : Level} {X : Type ℓ} → ℙ X → ℙ X → Type ℓ
A ⊂ B = ∀ x → x ∈ A → x ∈ B

intrinsic-open : {ℓ : Level} → (X : Type ℓ) → (U : ℙ X) → Type ℓ
intrinsic-open X U =
  (x y : X) → U x → (y ≡ x → ⊥) ⊎ U y

variable
  ℓ : Level
  X : Type ℓ

intrinsic-open-property :
  (U : ℙ X)
  → intrinsic-open X U
  → (x : X)
  → (x∈U : x ∈ U)
  → (λ y → (y ≡ x → ⊥) → ⊥) ⊂ U
intrinsic-open-property U O x x∈U y Py with O x y x∈U
...| inl ¬y≡x = byAbsurdity false
  where
  false : ⊥
  false = Py ¬y≡x
...| inr y∈U = y∈U
