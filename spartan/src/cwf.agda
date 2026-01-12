{-# OPTIONS --safe --without-K #-}
open import MLTT.Spartan hiding (_∘_; id)

module cwf where

record CwF : (𝓤 ⊔ 𝓥 ⊔ 𝓣 ⊔ 𝓦) ⁺  ̇ where
  field
    -- The collection of contexts
    Con      : 𝓤 ̇
    -- substitution
    Sub      : Con → Con → 𝓥 ̇
    -- composition
    _∘_      : ∀{Γ Δ} → Sub Δ Γ → ∀{Θ} → Sub Θ Δ → Sub Θ Γ
    -- associative
    assoc    : ∀{Γ Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ}{Ξ}{θ : Sub Ξ Θ} → ((γ ∘ δ) ∘ θ) ＝ (γ ∘ (δ ∘ θ))
    -- The identity substitution
    id       : ∀{Γ} → Sub Γ Γ
    idL      : ∀{Γ Δ}{γ : Sub Δ Γ} → (id ∘ γ) ＝ γ
    idR      : ∀{Γ Δ}{γ : Sub Δ Γ} → (γ ∘ id) ＝ γ
    -- terminal object
    ◇        : Con
    ε        : ∀{Γ} → Sub Γ ◇
    -- it's unique
    ◇η       : ∀{Γ}{σ : Sub Γ ◇} → σ ＝ (ε {Γ})

    Ty       : Con → 𝓣 ̇
    _[_]T    : ∀{Γ} → Ty Γ → ∀{Δ} → Sub Δ Γ → Ty Δ
    [∘]T     : ∀{Γ}{A : Ty Γ}{Δ}{γ : Sub Δ Γ}{Θ}{δ : Sub Θ Δ} → A [ γ ∘ δ ]T ＝ A [ γ ]T [ δ ]T
    [id]T    : ∀{Γ}{A : Ty Γ} → A [ id ]T ＝ A

    Tm       : (Γ : Con) → Ty Γ → 𝓦 ̇
    _[_]t    : ∀{Γ}{A : Ty Γ} → Tm Γ A → ∀{Δ}(γ : Sub Δ Γ) → Tm Δ (A [ γ ]T)

    _▷_      : (Γ : Con) → Ty Γ → Con
    _,[_]_   : ∀{Γ Δ}(γ : Sub Δ Γ) → ∀ {A A'} → A [ γ ]T ＝ A' → Tm Δ A' → Sub Δ (Γ ▷ A)
    p        : ∀{Γ A} → Sub (Γ ▷ A) Γ
    q        : ∀{Γ A} → Tm (Γ ▷ A) (A [ p ]T)
    ▷β₁      : ∀{Γ Δ}{γ : Sub Δ Γ}{A}{a : Tm Δ (A [ γ ]T)} → p ∘ (γ ,[ refl ] a) ＝ γ
    ▷η       : ∀{Γ Δ A}{γa : Sub Δ (Γ ▷ A)} → ((p ∘ γa) ,[ [∘]T ] (q [ γa ]t)) ＝ γa

  infixl 70 _∘_
  infixl 50 _,[_]_
  infixl 60 _[_]T _[_]t
  infixl 50 _▷_

-- Some definable stuffs
-- 1. β₂
-- 2. [∘]t
-- 3. and [id]t
-- can't be defined using ＝.
--
-- Using rewrite still can't work, because [id]T is neither a defined symbol nor a constructor.
