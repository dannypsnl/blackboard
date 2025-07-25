open import Cubical.Foundations.Prelude

module logic.intuitionistic-propositional-calculus where

PC1 : {A B : Type} → (A → (B → A))
PC1 = λ z z₁ → z

PC2 : {A B C : Type} → (A → (B → C)) → ((A → B) → (A → C))
PC2 = λ z z₁ z₂ → z z₂ (z₁ z₂)

MP : {A B : Type} → A → (A → B) → B
MP a f = f a

R : {A : Type} → A → A
R {A} = b {A} PC1
  where
    a : {B : Type} → (A → B) → (A → A)
    a = MP PC1 PC2
    b : {B : Type} → (A → (B → A)) → (A → A)
    b {B} = a {B → A}
