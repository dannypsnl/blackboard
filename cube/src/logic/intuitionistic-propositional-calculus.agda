open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

module logic.intuitionistic-propositional-calculus where

data Proposition : Type where
  ¬_ : Proposition → Proposition
  _∧_ _∨_ _⇒_ : Proposition → Proposition → Proposition
infixr 30 _⇒_
infixl 40 _∧_ _∨_
infix 50 ¬_

data ⊢ : Proposition → Type where
  PC1 : {A B : Proposition} → ⊢ (A ⇒ (B ⇒ A))
  PC2 : {A B C : Proposition} → ⊢ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C)))
  PC3 : {A B : Proposition} → ⊢ (A ⇒ (B ⇒ A ∧ B))
  PC4 : {A B : Proposition} → ⊢ (A ∧ B ⇒ A)
  PC5 : {A B : Proposition} → ⊢ (A ∧ B ⇒ B)
  PC6 : {A B : Proposition} → ⊢ (A ⇒ A ∨ B)
  PC7 : {A B : Proposition} → ⊢ (B ⇒ A ∨ B)
  PC8 : {A B C : Proposition} → ⊢ ((A ⇒ C) ⇒ ((B ⇒ C) ⇒ (A ∨ B ⇒ C)))
  PC9 : {A B : Proposition} → ⊢ ((A ⇒ B) ⇒ ((A ⇒ ¬ B) ⇒ ¬ A))
  PC10 : {A B : Proposition} → ⊢ (¬ A ⇒ (A ⇒ B))

  MP : {A B : Proposition} → ⊢ A → ⊢ (A ⇒ B) → ⊢ B

-- The followings are formalization of Borceux Vol3. Lemma 1.1.3
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

_≤_ : (A B : Proposition) → Type
A ≤ B = ⊢ (A ⇒ B)
infix 20 _≤_

∧-infimum : {A B C : Proposition} → C ≤ A → C ≤ B → C ≤ (A ∧ B)
∧-infimum {A}{B}{C} C≤A C≤B = MP C≤B (MP a PC2)
  where
    a : ⊢ (C ⇒ (B ⇒ A ∧ B))
    a = T C≤A PC3

record _×_ (A B : Type) : Type where
  field
    fst : A
    snd : B
infix 10 _×_

∧-symm : {A B : Proposition} → (A ∧ B) ≤ (B ∧ A) × (B ∧ A) ≤ (A ∧ B)
∧-symm {A}{B} = record { fst = MP PC4 b ; snd = MP PC4 b }
  where
    a : {A B : Proposition} → ⊢ (A ∧ B ⇒ (A ⇒ B ∧ A))
    a = T PC5 PC3
    b : {A B : Proposition} → ⊢ ((A ∧ B ⇒ A) ⇒ (A ∧ B ⇒ B ∧ A))
    b = MP a PC2

∨-supremum : {A B C : Proposition} → A ≤ C → B ≤ C → (A ∨ B) ≤ C
∨-supremum {A}{B}{C} A≤C B≤C = MP B≤C (MP A≤C PC8)

∨-symm : {A B : Proposition} → (A ∨ B) ≤ (B ∨ A) × (B ∨ A) ≤ (A ∨ B)
∨-symm {A}{B} = record { fst = a ; snd = a }
  where
    a : {A B : Proposition} → ⊢ ((A ∨ B) ⇒ (B ∨ A))
    a = MP PC6 (MP PC7 PC8)

terminal : {T X : Proposition} → ⊢ T → ⊢ (X ⇒ T)
terminal is-terminal = MP is-terminal PC1

initial : {T X : Proposition} → ⊢ T → ⊢ (¬ T ⇒ X)
initial {T}{X} is-terminal = MP d a
  where
    a : ⊢ (¬ ¬ T ⇒ (¬ T ⇒ X))
    a = PC10
    b : ⊢ ((¬ T ⇒ T) ⇒ ((¬ T ⇒ ¬ T) ⇒ ¬ ¬ T))
    b = PC9
    c : ⊢ ((¬ T ⇒ ¬ T) ⇒ ¬ ¬ T)
    c = MP (MP is-terminal PC1) b
    d : ⊢ (¬ ¬ T)
    d = MP R c

G : (A X : Proposition) → Proposition
G A X = X ∧ A

G-is-functor : {A X Y : Proposition} → X ≤ Y → G A X ≤ G A Y
G-is-functor {A}{X}{Y} X≤Y = MP PC5 d
  where
    a : ⊢ (X ∧ A ⇒ Y)
    a = T PC4 X≤Y
    b : ⊢ ((X ∧ A ⇒ Y) ⇒ (X ∧ A ⇒ (A ⇒ Y ∧ A)))
    b = MP (MP PC3 PC1) PC2
    c : ⊢ (X ∧ A ⇒ (A ⇒ Y ∧ A))
    c = MP a b
    d : ⊢ ((X ∧ A ⇒ A) ⇒ (X ∧ A ⇒ Y ∧ A))
    d = MP c PC2

F : (A X : Proposition) → Proposition
F A X = (A ⇒ X)

F-is-functor : {A X Y : Proposition} → X ≤ Y → F A X ≤ F A Y
F-is-functor {A}{X}{Y} X≤Y = MP (MP X≤Y PC1) PC2

F-is-right-adjoint-to-G : {A B : Proposition} → A ≤ F B (G B A) × G A (F A B) ≤ B
F-is-right-adjoint-to-G {A}{B} = record { fst = PC3 ; snd = MP PC5 (MP PC4 PC2) }
