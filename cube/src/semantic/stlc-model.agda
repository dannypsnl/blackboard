module semantic.stlc-model where

open import Cubical.Foundations.Prelude

variable
  ℓ ℓ' : Level

-- abstract model
record STLC (type : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  field
    el : type → Set ℓ'
    arr : type → type → type
    lam : {α β : type} → (el α → el β) → el (arr α β)
    app : {α β : type} → el (arr α β) → el α → el β
    arrβ : {α β : type} → {v : el α} → {y : el α → el β} → app (lam y) v ≡ y v
    arrη : {α β : type} → (u : el (arr α β)) → u ≡ lam (λ x → app u x)

-- fill an instance and show each component really works
simple : STLC Type
simple = record {
    el = λ x -> x;
    arr = λ x y → (x → y);
    lam = λ ty → ty;
    app = λ f x → f x;
    arrβ = refl;
    arrη = λ u → refl 
  }
