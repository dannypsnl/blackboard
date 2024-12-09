module algebra.monoid where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Relation.Binary

-- below is porting the code from
-- https://gist.github.com/doctorn/113296316492de304aff1dcd6a832294
-- but use cubical-agda
record Monoid : Type₁ where
  infix 5 _≈_
  infixr 15 _⊕_

  field
    A : Type
    _≈_ : Rel A A ℓ-zero

    isEquiv : BinaryRelation.isEquivRel _≈_

    𝟘 : A
    _⊕_ : A → A → A

    ⊕-cong₂ : ∀ {a b c d : A} → a ≈ b → c ≈ d → a ⊕ c ≈ b ⊕ d
    ⊕-assoc : ∀ a b c → (a ⊕ b) ⊕ c ≈ a ⊕ (b ⊕ c)
    ⊕-unitᵣ : ∀ a → a ⊕ 𝟘 ≈ a
    ⊕-unitₗ : ∀ a → 𝟘 ⊕ a ≈ a

  ∥_∥ : Type
  ∥_∥ = A

open Monoid using (∥_∥)

record IsHomomorphism (A B : Monoid) (f : ∥ A ∥ → ∥ B ∥) : Type₁ where
  private
    module A = Monoid A
    module B = Monoid B

  field
    hom-cong : ∀ {x y} → x A.≈ y → f x B.≈ f y

    𝟘-preserving : f A.𝟘 B.≈ B.𝟘
    ⊕-preserving : ∀ x y → f (x A.⊕ y) B.≈ f x B.⊕ f y

open IsHomomorphism

Homomorphism : (A B : Monoid) → Type₁
Homomorphism A B = Σ (∥ A ∥ → ∥ B ∥) (IsHomomorphism A B)

record IsBilinear (A B C : Monoid) (f : ∥ A ∥ → ∥ B ∥ → ∥ C ∥) : Set₁ where
  private
    module A = Monoid A
    module B = Monoid B
    module C = Monoid C

  flipped : ∥ B ∥ → ∥ A ∥ → ∥ C ∥
  flipped b a = f a b

  field
    left-linear : ∀ x → IsHomomorphism A C (flipped x)
    right-linear : ∀ x → IsHomomorphism B C (f x)

Bilinear : ∀ (A B C : Monoid) → Set₁
Bilinear A B C = Σ (∥ A ∥ → ∥ B ∥ → ∥ C ∥) (IsBilinear A B C)

infixr 15 _⊕_

-- Formal sums of pairs of elements
data Tensor (A B : Monoid) : Set where
  _·_ : ∥ A ∥ → ∥ B ∥ → Tensor A B
  _⊕_ : Tensor A B → Tensor A B → Tensor A B

module _ {A B : Monoid} where
  private
    module A = Monoid A
    module B = Monoid B

  ∅ : Tensor A B
  ∅ = A.𝟘 · B.𝟘

  infix 5 _~_

  -- Modulo the usual equations on tensors
  data _~_ : Rel (Tensor A B) (Tensor A B) ℓ-zero where
    ~-refl  : ∀ {x} → x ~ x
    ~-sym   : ∀ {x y} → x ~ y → y ~ x
    ~-trans : ∀ {x y z} → x ~ y → y ~ z → x ~ z

    ⊕-cong₂ : ∀ {x₁ x₂ y₁ y₂} → x₁ ~ x₂ → y₁ ~ y₂ → x₁ ⊕ y₁ ~ x₂ ⊕ y₂
    ⊕-assoc : ∀ x y z → (x ⊕ y) ⊕ z ~ x ⊕ (y ⊕ z)
    ⊕-unitᵣ : ∀ x → x ⊕ ∅ ~ x
    ⊕-unitₗ : ∀ x → ∅ ⊕ x ~ x

    ·-cong₂ : ∀ {x₁ x₂ y₁ y₂} → x₁ A.≈ x₂ → y₁ B.≈ y₂ → x₁ · y₁ ~ x₂ · y₂
    ·-linearₗ : ∀ {x₁ x₂ y} → (x₁ A.⊕ x₂) · y ~ (x₁ · y) ⊕ (x₂ · y)
    ·-linearᵣ : ∀ {x y₁ y₂} → x · (y₁ B.⊕ y₂) ~ (x · y₁) ⊕ (x · y₂)
    ·-unitₗ : ∀ y → A.𝟘 · y ~ ∅
    ·-unitᵣ : ∀ x → x · B.𝟘 ~ ∅

_⊗_ : (A B : Monoid) → Monoid
A ⊗ B = record
  { A = Tensor A B
  ; _≈_ = _~_
  ; 𝟘 = A.𝟘 · B.𝟘
  ; _⊕_ = _⊕_
  ; isEquiv = BinaryRelation.equivRel (λ x → ~-refl) (λ a b x → ~-sym x) (λ a b c p1 p2 → ~-trans p1 p2)
  ; ⊕-cong₂ = ⊕-cong₂
  ; ⊕-assoc = ⊕-assoc
  ; ⊕-unitᵣ = ⊕-unitᵣ
  ; ⊕-unitₗ = ⊕-unitₗ
  }
  where module A = Monoid A
        module B = Monoid B
