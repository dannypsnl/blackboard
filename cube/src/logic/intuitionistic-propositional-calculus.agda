open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)

module logic.intuitionistic-propositional-calculus where

data Proposition : Type where
  ⊤ ⊥ : Proposition
  ¬_ : Proposition → Proposition
  _∧_ _∨_ _⇒_ : Proposition → Proposition → Proposition
infixr 30 _⇒_
infixl 40 _∧_ _∨_
infix 50 ¬_

data ⊢ : Proposition → Type where
  truth : ⊢ ⊤
  truth-unique : {T : Proposition} → ⊤ ≡ T → ⊢ T
  false-elim : (X : Proposition) → ⊢ (⊥ ⇒ X)

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
F A X = A ⇒ X

F-is-functor : {A X Y : Proposition} → X ≤ Y → F A X ≤ F A Y
F-is-functor {A}{X}{Y} X≤Y = MP (MP X≤Y PC1) PC2

F-is-right-adjoint-to-G : {A B : Proposition} → A ≤ F B (G B A) × G A (F A B) ≤ B
F-is-right-adjoint-to-G {A}{B} = record { fst = f ; snd = s }
  where
    f : A ≤ B ⇒ (A ∧ B)
    f = PC3
    s : (A ⇒ B) ∧ A ≤ B
    s = MP PC5 (MP PC4 PC2)

-- Lemma 1.1.4
F' : (A X : Proposition) → Proposition
F' A X = X ⇒ A

F'-is-contra-functor : {A X Y : Proposition} → X ≤ Y → F' A Y ≤ F' A X
F'-is-contra-functor {A}{X}{Y} X≤Y = target
  where
    pp : ⊢ ((Y ⇒ A) ∧ X ⇒ (Y ⇒ A))
    pp = PC4
    pp' : ⊢ (((Y ⇒ A) ∧ X ⇒ Y) ⇒ ((Y ⇒ A) ∧ X ⇒ A))
    pp' = MP pp PC2

    outY : ⊢ ((Y ⇒ A) ∧ X ⇒ Y)
    outY = T PC5 X≤Y

    pre : (Y ⇒ A) ∧ X ≤ A
    pre = MP outY pp'

    lemma : (Y ⇒ A) ∧ X ≤ A → Y ⇒ A ≤ X ⇒ A
    lemma P = T k c
      where
        k : ⊢ ((Y ⇒ A) ⇒ (X ⇒ (Y ⇒ A) ∧ X))
        k = PC3
        c : ⊢ ((X ⇒ (Y ⇒ A) ∧ X) ⇒ (X ⇒ A))
        c = MP (MP P PC1) PC2

    target : ⊢ ((Y ⇒ A) ⇒ (X ⇒ A))
    target = lemma pre

⊥≅¬⊤ : ⊥ ≤ ¬ ⊤ × ¬ ⊤ ≤ ⊥
⊥≅¬⊤ = record { fst = false-elim (¬ ⊤) ; snd = initial truth }

-- Here I define ⊥ := ¬ ⊤ to simplify proof.
X⇒⊥-iso-¬X : {X : Proposition} → ¬ X ≤ X ⇒ ¬ ⊤ × X ⇒ ¬ ⊤ ≤ ¬ X
X⇒⊥-iso-¬X {X} = record { fst = PC10 ; snd = MP (terminal truth) PC9 }

module _
  (ax1 : {T : Proposition} → ⊢ T → ⊤ ≡ T)
  (ax2 : {A B : Proposition} → A ≤ B → B ≤ A → A ≡ B)
  where

  variable
    A B : Proposition

  -- Proposition 1.2.3 condition 1
  p1-2-3-c1-forward : A ≤ B → ⊤ ≡ A ⇒ B
  p1-2-3-c1-forward P = ax1 P
  p1-2-3-c1-backward : ⊤ ≡ A ⇒ B → A ≤ B
  p1-2-3-c1-backward P = truth-unique P

  -- Proposition 1.2.7 condition 1
  p1-2-7-c1 : ⊤ ≤ (⊥ ⇒ ⊥)
  p1-2-7-c1 = MP (false-elim ⊥) PC1

  -- Proposition 1.2.7 condition 2
  p1-2-7-c2 : {A B : Proposition} → A ≤ B → ¬ B ≤ ¬ A
  p1-2-7-c2 {A}{B} A≤B = T PC10 (T (lemma pre) lemma2')
    where
      pre : (B ⇒ ⊥) ∧ A ≤ ⊥
      pre = MP ((T PC5 A≤B)) (MP PC4 PC2)
      
      lemma : (B ⇒ ⊥) ∧ A ≤ ⊥ → B ⇒ ⊥ ≤ A ⇒ ⊥
      lemma P = T PC3 (MP (MP P PC1) PC2)

      left : ¬ ⊤ ≤ ⊥
      left = initial truth
      right : ⊥ ≤ ¬ ⊤
      right = false-elim (¬ ⊤)
      eq : ¬ ⊤ ≡ ⊥
      eq = ax2 left right

      lemma2 : A ⇒ ¬ ⊤ ≤ ¬ A
      lemma2 = MP (MP truth PC1) PC9
      lemma2' : A ⇒ ⊥ ≤ ¬ A
      lemma2' = subst (λ z → A ⇒ z ≤ ¬ A) eq (MP (MP truth PC1) PC9)
