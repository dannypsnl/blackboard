open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Sigma hiding (_∧_; _∨_)

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

_≤_ : (A B : Proposition) → Type
A ≤ B = ⊢ (A ⇒ B)
infix 20 _≤_

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

∧-infimum : {A B C : Proposition} → C ≤ A → C ≤ B → C ≤ (A ∧ B)
∧-infimum {A}{B}{C} C≤A C≤B = MP C≤B (MP a PC2)
  where
    a : ⊢ (C ⇒ (B ⇒ A ∧ B))
    a = T C≤A PC3

∨-supremum : {A B C : Proposition} → A ≤ C → B ≤ C → (A ∨ B) ≤ C
∨-supremum {A}{B}{C} A≤C B≤C = MP B≤C (MP A≤C PC8)

module _ (iff : {A B : Proposition} → A ≤ B → B ≤ A → A ≡ B) where
  ∧-symm : {A B : Proposition} → (A ∧ B) ≡ (B ∧ A)
  ∧-symm {A}{B} = iff (MP PC4 b) (MP PC4 b)
    where
      a : {A B : Proposition} → ⊢ (A ∧ B ⇒ (A ⇒ B ∧ A))
      a = T PC5 PC3
      b : {A B : Proposition} → ⊢ ((A ∧ B ⇒ A) ⇒ (A ∧ B ⇒ B ∧ A))
      b = MP a PC2
  ∨-symm : {A B : Proposition} → (A ∨ B) ≡ (B ∨ A)
  ∨-symm {A}{B} = iff a a
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
F-is-right-adjoint-to-G {A}{B} = f , s
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
⊥≅¬⊤ = false-elim (¬ ⊤) , initial truth

-- Here I define ⊥ := ¬ ⊤ to simplify proof.
X⇒⊥-iso-¬X : {X : Proposition} → ¬ X ≤ X ⇒ ¬ ⊤ × X ⇒ ¬ ⊤ ≤ ¬ X
X⇒⊥-iso-¬X {X} = PC10 , MP (terminal truth) PC9

prod : {P Q R : Proposition} → P ≤ Q → P ≤ R → P ≤ Q ∧ R
prod {P}{Q}{R} P1 P2 = MP P2 (MP d e)
  where
  a : P ≤ (Q ⇒ R ⇒ Q ∧ R)
  a = MP PC3 PC1
  b : P ⇒ (Q ⇒ R ⇒ Q ∧ R) ≤ (P ⇒ Q) ⇒ (P ⇒ (R ⇒ Q ∧ R))
  b = PC2
  c : (P ⇒ Q) ≤ (P ⇒ (R ⇒ Q ∧ R))
  c = MP a b
  d : ⊢ (P ⇒ (R ⇒ Q ∧ R))
  d = MP P1 c
  e : P ⇒ (R ⇒ Q ∧ R) ≤ (P ⇒ R) ⇒ (P ⇒ Q ∧ R)
  e = PC2

module _
  (iff : {A B : Proposition} → A ≤ B → B ≤ A → A ≡ B)
  (adj1 : {A B C : Proposition} → A ∧ B ≤ C → A ≤ B ⇒ C)
  (adj2 : {A B C : Proposition} → A ≤ B ⇒ C → A ∧ B ≤ C)
  where
  variable
    A B C : Proposition

  ¬⊤≡⊥ : ¬ ⊤ ≡ ⊥
  ¬⊤≡⊥ = iff (initial truth) (false-elim (¬ ⊤))

  ⊤≡¬⊥ : ⊤ ≡ ¬ ⊥
  ⊤≡¬⊥ = iff (terminal (MP (false-elim (¬ ⊤)) (MP (false-elim ⊤) PC9))) (MP truth PC1)

  valid-is-⊤ : {T : Proposition} → ⊢ T → ⊤ ≡ T
  valid-is-⊤ {T} T-valid = iff (MP T-valid PC1) (MP truth PC1)

  -- Proposition 1.2.3
  -- condition 1
  p1-2-3-c1-forward : A ≤ B → ⊤ ≡ A ⇒ B
  p1-2-3-c1-forward P = valid-is-⊤ P
  p1-2-3-c1-backward : ⊤ ≡ A ⇒ B → A ≤ B
  p1-2-3-c1-backward P = truth-unique P
  -- condition 2
  p1-2-3-c2 : A ≡ ⊤ ⇒ A
  p1-2-3-c2 = iff PC1 right
    where
    right : ⊤ ⇒ A ≤ A
    right = MP truth (adj1 (MP PC4 (MP PC5 PC2)))
  -- condition 3
  p1-2-3-c3 : A ⇒ B ∧ C ≡ (A ⇒ B) ∧ (A ⇒ C)
  p1-2-3-c3 = iff left right
    where
    t : A ⇒ B ∧ C ≤ A ⇒ B
    t = MP (MP PC4 PC1) PC2
    t2 : A ⇒ B ∧ C ≤ A ⇒ C
    t2 = MP (MP PC5 PC1) PC2
    left : A ⇒ B ∧ C ≤ (A ⇒ B) ∧ (A ⇒ C)
    left = prod t t2

    j : ⊢ (A ⇒ (B ⇒ (C ⇒ B ∧ C)))
    j = MP PC3 PC1
    c : (A ⇒ (B ⇒ (C ⇒ B ∧ C))) ≤ ((A ⇒ B) ⇒ (A ⇒ (C ⇒ B ∧ C)))
    c = PC2
    d : (A ⇒ B) ≤ (A ⇒ (C ⇒ B ∧ C))
    d = MP j c
    e : (A ⇒ (C ⇒ B ∧ C)) ≤ (A ⇒ C) ⇒ A ⇒ B ∧ C
    e = PC2
    right : (A ⇒ B) ∧ (A ⇒ C) ≤ A ⇒ B ∧ C
    right = adj2 (T d e)

  -- Proposition 1.2.7
  -- condition 1
  p1-2-7-c1 : ⊤ ≤ (⊥ ⇒ ⊥)
  p1-2-7-c1 = MP (false-elim ⊥) PC1
  -- condition 2
  p1-2-7-c2 : {A B : Proposition} → A ≤ B → ¬ B ≤ ¬ A
  p1-2-7-c2 {A}{B} A≤B = T PC10 (T (lemma pre) lemma2')
    where
      pre : (B ⇒ ⊥) ∧ A ≤ ⊥
      pre = MP ((T PC5 A≤B)) (MP PC4 PC2)

      lemma : (B ⇒ ⊥) ∧ A ≤ ⊥ → B ⇒ ⊥ ≤ A ⇒ ⊥
      lemma P = T PC3 (MP (MP P PC1) PC2)

      lemma2 : A ⇒ ¬ ⊤ ≤ ¬ A
      lemma2 = MP (MP truth PC1) PC9
      lemma2' : A ⇒ ⊥ ≤ ¬ A
      lemma2' = subst (λ z → A ⇒ z ≤ ¬ A) ¬⊤≡⊥ (MP (MP truth PC1) PC9)
  -- condition 5
  p1-2-7-c5 : ¬ A ∨ B ≤ A ⇒ B
  p1-2-7-c5 = MP PC1 (MP PC10 PC8)
