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
  -- This is about Proposition 1.2.2, skipped here and assume it
  (distrib : {A B C : Proposition} → A ∧ (B ∨ C) ≡ (A ∧ B) ∨ (A ∧ C))
  where
  variable
    A B C : Proposition

  ∧-assoc : {A B C : Proposition} → A ∧ B ∧ C ≡ A ∧ (B ∧ C)
  ∧-assoc {A}{B}{C} = iff l r
    where
    l1 : A ∧ B ∧ C ≤ A
    l1 = T PC4 PC4
    l2 : A ∧ B ∧ C ≤ B
    l2 = T PC4 PC5
    l3 : A ∧ B ∧ C ≤ C
    l3 = PC5
    l : A ∧ B ∧ C ≤ A ∧ (B ∧ C)
    l = prod l1 (prod l2 l3)

    r1 : A ∧ (B ∧ C) ≤ A
    r1 = PC4
    r2 : A ∧ (B ∧ C) ≤ B
    r2 = T PC5 PC4
    r3 : A ∧ (B ∧ C) ≤ C
    r3 = T PC5 PC5
    r : A ∧ (B ∧ C) ≤ A ∧ B ∧ C
    r = prod (prod r1 r2) r3

  ¬⊤≡⊥ : ¬ ⊤ ≡ ⊥
  ¬⊤≡⊥ = iff (initial truth) (false-elim (¬ ⊤))

  ⊤≡¬⊥ : ⊤ ≡ ¬ ⊥
  ⊤≡¬⊥ = iff (terminal (MP (false-elim (¬ ⊤)) (MP (false-elim ⊤) PC9))) (MP truth PC1)

  valid-is-⊤ : {T : Proposition} → ⊢ T → ⊤ ≡ T
  valid-is-⊤ {T} T-valid = iff (MP T-valid PC1) (MP truth PC1)

  ¬X≡X⇒⊥ : {X : Proposition} → ¬ X ≡ X ⇒ ⊥
  ¬X≡X⇒⊥ {X} = iff PC10 b
    where
      a : X ⇒ ¬ ⊤ ≤ ¬ X
      a = MP (MP truth PC1) PC9
      b : X ⇒ ⊥ ≤ ¬ X
      b = subst (λ x → X ⇒ x ≤ ¬ X) ¬⊤≡⊥ a

  -- Proposition 1.2.3
  -- condition 1
  p1-2-3-c1 : (A ≤ B → ⊤ ≡ A ⇒ B) × (⊤ ≡ A ⇒ B → A ≤ B)
  p1-2-3-c1 = (λ P → valid-is-⊤ P) , (λ P → truth-unique P)
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
  
  -- Proposition 1.2.4
  -- condition 2
  p1-2-4-c2 : (B ⇒ C) ∧ B ≤ C
  p1-2-4-c2 = adj2 R

  -- Proposition 1.2.6
  -- condition 2
  p1-2-6-c2 : ¬ B ∧ B ≡ ⊥
  p1-2-6-c2 {B} = iff proof1 (false-elim (¬ B ∧ B))
    where
      t : (B ⇒ ⊥) ∧ B ≤ ⊥
      t = p1-2-4-c2 {B}{⊥}
      proof1 : ¬ B ∧ B ≤ ⊥
      proof1 = subst (λ x → x ∧ B ≤ ⊥) (sym ¬X≡X⇒⊥) t
      proof2 : ¬ B ∧ B ≤ ⊥
      proof2 = adj2 PC10

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
  -- condition 3
  p1-2-7-c3 : {A : Proposition} → A ⇒ ⊥ ≡ ((A ⇒ ⊥) ⇒ ⊥) ⇒ ⊥
  p1-2-7-c3 {A} = iff l r
    where
    l : A ⇒ ⊥ ≤ ((A ⇒ ⊥) ⇒ ⊥) ⇒ ⊥
    l = adj1 (MP PC4 (MP PC5 PC2))

    a : A ≤ (A ⇒ ⊥) ⇒ ⊥
    a = adj1 (MP PC4 (MP PC5 PC2))
    b : ¬ ((A ⇒ ⊥) ⇒ ⊥) ≤ ¬ A
    b = p1-2-7-c2 a
    c : ¬ ((A ⇒ ⊥) ⇒ ⊥) ≤ A ⇒ ⊥
    c = subst (λ x → ¬ ((A ⇒ ⊥) ⇒ ⊥) ≤ x) ¬X≡X⇒⊥ b
    r : ((A ⇒ ⊥) ⇒ ⊥) ⇒ ⊥ ≤ A ⇒ ⊥
    r = subst (λ x → x ≤ A ⇒ ⊥) ¬X≡X⇒⊥ c
  -- condition 4
  p1-2-7-c4 : ¬ (A ∨ B) ≡ ¬ A ∧ ¬ B
  p1-2-7-c4 {A}{B} = iff l r
    where
    l : ¬ (A ∨ B) ≤ ¬ A ∧ ¬ B
    l = prod (p1-2-7-c2 PC6) (p1-2-7-c2 PC7)

    r8 : (¬ B ∧ ⊥) ∨ (¬ A ∧ ⊥) ≤ ⊥
    r8 = MP PC5 (MP PC5 PC8)
    r7 : (¬ B ∧ ⊥) ∨ (¬ A ∧ (¬ B ∧ B)) ≤ ⊥
    r7 = subst (λ x → (¬ B ∧ ⊥) ∨ (¬ A ∧ x) ≤ ⊥) (sym p1-2-6-c2) r8
    r6 : (¬ B ∧ (¬ A ∧ A)) ∨ (¬ A ∧ (¬ B ∧ B)) ≤ ⊥
    r6 = subst (λ x → (¬ B ∧ x) ∨ (¬ A ∧ (¬ B ∧ B)) ≤ ⊥) (sym p1-2-6-c2) r7
    r5 : (¬ B ∧ (¬ A ∧ A)) ∨ (¬ A ∧ ¬ B ∧ B) ≤ ⊥
    r5 = subst (λ x → (¬ B ∧ (¬ A ∧ A)) ∨ x ≤ ⊥) (sym ∧-assoc) r6
    r4 : (¬ B ∧ ¬ A ∧ A) ∨ (¬ A ∧ ¬ B ∧ B) ≤ ⊥
    r4 = subst (λ x → x ∨ (¬ A ∧ ¬ B ∧ B) ≤ ⊥) (sym ∧-assoc) r5
    r3 : (¬ A ∧ ¬ B ∧ A) ∨ (¬ A ∧ ¬ B ∧ B) ≤ ⊥
    r3 = subst (λ x → (x ∧ A) ∨ (¬ A ∧ ¬ B ∧ B) ≤ ⊥) (∧-symm iff) r4
    r2 : ¬ A ∧ ¬ B ∧ (A ∨ B) ≤ ⊥
    r2 = subst (λ x → x ≤ ⊥) (sym distrib) r3
    r1 : ¬ A ∧ ¬ B ≤ (A ∨ B) ⇒ ⊥
    r1 = adj1 r2
    r : ¬ A ∧ ¬ B ≤ ¬ (A ∨ B)
    r = subst (λ x → ¬ A ∧ ¬ B ≤ x) (sym ¬X≡X⇒⊥) r1
  -- condition 5
  p1-2-7-c5 : ¬ A ∨ B ≤ A ⇒ B
  p1-2-7-c5 = MP PC1 (MP PC10 PC8)

  -- Proposition 1.2.8
  p1-2-8-c1 : A ≤ B → ¬ ¬ A ≤ ¬ ¬ B
  p1-2-8-c1 A≤B = p1-2-7-c2 (p1-2-7-c2 A≤B)
  p1-2-8-c2 : A ≤ ¬ ¬ A
  p1-2-8-c2 {A} = subst (λ x → A ≤ x) (sym (a ∙ b)) r
    where
    a : ¬ (¬ A) ≡ (¬ A) ⇒ ⊥
    a = ¬X≡X⇒⊥ {¬ A}
    b : (¬ A) ⇒ ⊥ ≡ (A ⇒ ⊥) ⇒ ⊥
    b = congS (λ x → x ⇒ ⊥) ¬X≡X⇒⊥

    p : (A ⇒ ⊥) ∧ A ≤ ⊥
    p = adj2 (MP (adj1 PC5) PC2)
    r : A ≤ (A ⇒ ⊥) ⇒ ⊥
    r = adj1 (subst (λ x → x ≤ ⊥) (∧-symm iff) p)
  p1-2-8-c3 : (¬ ¬ ⊥ ≡ ⊥) × (¬ ¬ ⊤ ≡ ⊤)
  p1-2-8-c3 = iff l (false-elim (¬ (¬ ⊥))) , iff (MP truth PC1) r
    where
    l2 : ⊥ ≤ ⊥
    l2 = R
    l1 : ¬ ⊤ ≤ ⊥
    l1 = subst (λ x → x ≤ ⊥) (sym ¬⊤≡⊥) l2
    l : ¬ (¬ ⊥) ≤ ⊥
    l = subst (λ x → ¬ x ≤ ⊥) ⊤≡¬⊥ l1

    r2 : ⊤ ≤ ⊤
    r2 = R
    r1 : ⊤ ≤ ¬ ⊥
    r1 = subst (λ x → ⊤ ≤ x) ⊤≡¬⊥ r2
    r : ⊤ ≤ ¬ (¬ ⊤)
    r = subst (λ x → ⊤ ≤ ¬ x) (sym ¬⊤≡⊥) r1
