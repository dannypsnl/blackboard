{-
This file is from https://gist.github.com/yangzhixuan/e5ddf138f073d4ea76706ccfa130a8b9
I copy purely for a record, this file shows that by using `lam` and `IsExt` (and syntax wrapping),
we can have a way to express terms that similar to HOAS:
> K₁ : Γ ⊢ τ ⇒ (σ ⇒ τ)
> K₁ = lam (λ a → lam (λ b → a))
-}


{-# OPTIONS --no-import-sorts #-}

open import Agda.Primitive
  renaming (Set to Type; Setω to Typeω)
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

module easier-indicies where

variable
  A B C : Type

data List (A : Type) : Type where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A
infixr 5 _∷_
_,_ : List A → A → List A
xs , x = x ∷ xs

variable
  x y   : A
  xs ys : List A

data _∋_ {A : Type} : List A → A → Type where
  zero : (x ∷ xs) ∋ x
  suc : xs ∋ x → (y ∷ xs) ∋ x
infix 4 _∋_

------------------------------------------------------------------------------
-- Types for STLC
data Ty (V : Type) : Type where
  `_ : V → Ty V
  _⇒_ : (τ σ : Ty V) → Ty V
-- Convention: τ₁ ⇒ τ₂ ⇒ ... τₙ ≡ τ₁ ⇒ (τ₂ ⇒ (... ⇒ τₙ))
infixr 7 _⇒_

------------------------------------------------------------------------------
-- Context in STLC
Cxt : Type → Type
Cxt V = List (Ty V)

variable
  V   : Type
  τ σ : Ty V
  Γ Δ : Cxt V
  
------------------------------------------------------------------------------
-- Intrinsically-typed de Bruijn representation of STLC
--

infix 4 _⊢_
data _⊢_ {V : Type} : Cxt V → Ty V → Type where
  `_ : Γ ∋ τ → Γ ⊢ τ
  _·_ : Γ ⊢ (τ ⇒ σ) → Γ ⊢ τ → Γ ⊢ σ
  ƛ_ : (Γ , τ) ⊢ σ → Γ ⊢ τ ⇒ σ

infixl 6 _·_
infixr 5 ƛ_

Ren : {V : Type} → Cxt V → Cxt V → Type
Ren {V} Γ Δ = {τ : Ty V} → Γ ∋ τ → Δ ∋ τ

ext : Ren Γ Δ → Ren (Γ , τ) (Δ , τ)
ext ρ zero    = zero
ext ρ (suc x) = suc (ρ x)

rename
  : {V : Type} {Γ Δ : Cxt V} 
  → ({τ : Ty V} → Γ ∋ τ → Δ ∋ τ)
  → {τ : Ty V}
  → Γ ⊢ τ → Δ ⊢ τ
rename ρ (` x)   = ` ρ x
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (ƛ M)   = ƛ rename (ext ρ) M

inc : Ren Γ (Γ , σ)
inc x = suc x

weaken : Γ ⊢ τ → (Γ , σ) ⊢ τ
weaken M = rename suc M

-- HOAS-like smart constructor for lambda abstraction
record IsExt {V : Type} (Δ Γ : Cxt V) : Type₁ where
  field
    applySub : {τ : Ty V} → Γ ⊢ τ → Δ ⊢ τ

open IsExt {{...}} public

instance
  idExt : {V : Type} {Γ : Cxt V} → IsExt Γ Γ
  idExt .applySub t = t

  wkExt : {V : Type} {Γ : Cxt V} {τ : Ty V} → IsExt (Γ , τ) Γ
  wkExt .applySub t = weaken t

lam : {V : Type} {Γ : Cxt V} {τ σ : Ty V}
    → (({Δ : Cxt V} → {{IsExt Δ (Γ , τ)}} → Δ ⊢ τ)
         → (Γ , τ) ⊢ σ)
    → Γ ⊢ τ ⇒ σ
lam body = ƛ (body (applySub (` zero)))

syntax lam (λ x → t) = λ[ x ] t


-- Example terms

_ : Γ ⊢ τ ⇒ (σ ⇒ τ)
_ = lam (λ a → lam (λ b → a))

K₁ : Γ ⊢ τ ⇒ (σ ⇒ τ)
K₁ = λ[ a ] λ[ b ] a

I : Γ ⊢ τ ⇒ τ
I = λ[ x ] x

c₂ : Γ ⊢ (τ ⇒ τ) ⇒ τ ⇒ τ
c₂ = λ[ f ] λ[ x ] (f · (f · x))
