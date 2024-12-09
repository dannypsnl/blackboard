open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

-- https://unimath.github.io/SymmetryBook/book.pdf
module symmetry-ch2 where

variable
  ℓ : Level
  T P : Type ℓ

-- exercise-2-16-6 : (x : ∥ T ∥₁) → ∃[ t ∈ T ] (x ≡ ∣ t ∣₁)
-- exercise-2-16-6 ∣ x ∣₁ = {!   !} 
-- exercise-2-16-6 (squash₁ x x₁ i) = {!   !}

exercise-2-16-7 : isProp P → ∥ P ∥₁ ≃ P
exercise-2-16-7 {P = P} hP = isoToEquiv f
  where
  f : Iso ∥ P ∥₁ P
  Iso.fun f        = rec hP (idfun P)
  Iso.inv f x      = ∣ x ∣₁
  Iso.rightInv f _ = refl
  Iso.leftInv f    = elim
    (λ a → isProp→isSet isPropPropTrunc (Iso.inv f (Iso.fun f a)) a)
    (λ _ → refl)
