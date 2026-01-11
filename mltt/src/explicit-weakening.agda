{-# OPTIONS --rewriting #-}
-- https://arxiv.org/abs/2412.03124
module explicit-weakening where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

-- STLC
data Type : Set where
  base : Type
  _⇒_ : Type → Type → Type
infixr 7 _⇒_

variable
  A B C : Type

data Con : Set where
  ∅ : Con
  _▷_ : Con → Type → Con
infixl 5 _▷_

variable
  Γ Δ Θ Ξ : Con

data _⊢_ : Con → Type → Set where
  -- here
  • : Γ ▷ A ⊢ A
  -- weakening
  _↑ : (M : Γ ⊢ B)
      --------------
      → Γ ▷ A ⊢ B
  -- abs
  ƛ_ : (N : Γ ▷ A ⊢ B)
      ------------------
      → Γ ⊢ A ⇒ B
  -- app
  _·_ : (L : Γ ⊢ A ⇒ B) (M : Γ ⊢ A)
      ---------------------------------
      → Γ ⊢ B
infix 5 ƛ_
infix 4 _⊢_
infixl 7 _·_

variable
  L M N P Q : Γ ⊢ A

-- substitution
data _⊨_ : Con → Con → Set where
  id : Δ ⊨ Δ
  -- weakening
  _↑ : (σ : Γ ⊨ Δ) → Γ ▷ A ⊨ Δ
  _▷_ : (σ : Γ ⊨ Δ)
         (M : Γ ⊢ A)
        ---------------
        → Γ ⊨ Δ ▷ A
infix 4  _⊨_
infix 8 _↑

variable
  σ τ υ : Γ ⊨ Δ

pattern △ = _ ▷ _

-- Instantiation
_[_] : (M : Δ ⊢ A) (σ : Γ ⊨ Δ) → Γ ⊢ A
M [ id ] = M
M [ σ ↑ ] = (M [ σ ]) ↑
• [ σ ▷ P ] = P
(M ↑) [ σ ▷ P ] = M [ σ ]
(ƛ M) [ σ @ △ ] = ƛ (M [ σ ↑ ▷ • ])
(L · M) [ σ @ △ ] = L [ σ ] · (M [ σ ])

_⨟_ : (σ : Θ ⊨ Δ) (τ : Γ ⊨ Θ) → Γ ⊨ Δ
σ ⨟ id = σ
σ ⨟ (τ ↑) = (σ ⨟ τ) ↑
id ⨟ τ @ △ = τ
(σ ↑) ⨟ (τ ▷ Q) = σ ⨟ τ
(σ ▷ P) ⨟ τ @ △ = (σ ⨟ τ) ▷ (P [ τ ])
infixl 5 _⨟_

[][] : (M : Δ ⊢ A)
       (σ : Θ ⊨ Δ)
       (τ : Γ ⊨ Θ)
       → M [ σ ] [ τ ] ≡ M [ σ ⨟ τ ]
[][] M σ id = refl
[][] M σ (τ ↑) = cong _↑ ([][] M σ τ)
[][] M id (τ ▷ M₁) = refl
[][] M (σ ↑) (τ ▷ M₁) = [][] M σ τ
[][] • (σ ▷ P) τ@△ = refl
[][] (M ↑) (σ ▷ P) τ@△ = [][] M σ τ
[][] (ƛ N) σ@△ τ@△ = cong ƛ_ ([][] N (σ ↑ ▷ •) (τ ↑ ▷ •))
[][] (L · M) σ@△ τ@△ = cong₂ _·_ ([][] L σ τ) ([][] M σ τ)
{-# REWRITE [][] #-}

-- 2.10 Composition has a left identity
left-id : (τ : Γ ⊨ Δ) → id ⨟ τ ≡ τ
left-id id = refl
left-id (τ ↑) = cong _↑ (left-id τ)
left-id (τ ▷ Q) = refl
{-# REWRITE left-id #-}

-- 2.11 Composition is associative
assoc : (σ : Θ ⊨ Δ)
        (τ : Ξ ⊨ Θ)
        (υ : Γ ⊨ Ξ)
        → (σ ⨟ τ) ⨟ υ ≡ σ ⨟ (τ ⨟ υ)
assoc σ τ id = refl
assoc σ τ (υ ↑) = cong _↑ (assoc σ τ υ)
assoc σ id (υ ▷ M) = refl
assoc σ (τ ↑) (υ ▷ M) = assoc σ τ υ
assoc id (τ ▷ M₁) (υ ▷ M) = refl
assoc (σ ↑) (τ ▷ M₁) (υ ▷ M) = assoc σ τ (υ ▷ M)
assoc (σ ▷ M₂) (τ ▷ M₁) (υ ▷ M) = cong₂ _▷_ (assoc σ (τ ▷ M₁) (υ ▷ M)) refl
{-# REWRITE assoc #-}

-- 3.1 Special cases of substitution
_[_]₀ : (N : Γ ▷ A ⊢ B)
        (M : Γ ⊢ A)
        ------------
        → Γ ⊢ B
N [ M ]₀ = N [ id ▷ M ]

_[_]₁ : (N : Γ ▷ A ▷ B ⊢ C)
        (M : Γ ⊢ A)
        ------------
        → Γ ▷ B ⊢ C
N [ M ]₁ = N [ (id ▷ M) ↑ ▷ • ]

-- Challenging examples in PLFA, but trivial here
double-subst : N [ M ]₁ [ L ]₀ ≡ N [ L ↑ ]₀ [ M ]₀
double-subst = refl
commute-subst : N [ M ]₀ [ L ]₀ ≡ N [ L ]₁ [ M [ L ]₀ ]₀
commute-subst = refl

-- Drawback:  identifying when terms are equivalent may become more difficult
