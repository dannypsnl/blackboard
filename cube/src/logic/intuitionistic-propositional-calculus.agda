open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

module logic.intuitionistic-propositional-calculus where

data Proposition : Type where
  _∧_ _∨_ _⇒_ : Proposition → Proposition → Proposition
infixr 8 _⇒_

data ⊢ : Proposition → Type where
  PC1 : {A B : Proposition} → ⊢ (A ⇒ (B ⇒ A))
  PC2 : {A B C : Proposition} → ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  MP : {A B : Proposition} → ⊢ A → ⊢ (A ⇒ B) → ⊢ B

R : {A : Proposition} → ⊢ (A ⇒ A)
R {A} = MP PC1 (b {A})
  where
    a : {B : Proposition} → ⊢ ((A ⇒ B) ⇒ (A ⇒ A))
    a = MP PC1 PC2
    b : {B : Proposition} → ⊢ ((A ⇒ (B ⇒ A)) ⇒ (A ⇒ A))
    b {B} = a {B ⇒ A}

T : {A B C : Proposition} → ⊢ (A ⇒ B) → ⊢ (B ⇒ C) → ⊢ (A ⇒ C)
T {A} {B} {C} A≤B B≤C = MP A≤B (MP b PC2)
  where
    a : ⊢ ((B ⇒ C) ⇒ (A ⇒ (B ⇒ C)))
    a = PC1
    b : ⊢ (A ⇒ (B ⇒ C))
    b = MP B≤C PC1
