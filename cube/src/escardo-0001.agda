open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Functions.Fixpoint
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥; uninhabEquiv)
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

-- https://mathstodon.xyz/@MartinEscardo/113188732092479662
module escardo-0001 where

variable
  ℓ : Level
  X A : Type ℓ
  B : A → Type ℓ

-- Any type X with designated point x₀ has a propositional-truncation
designated-point=>truncation : X → ∥ X ∥₁
designated-point=>truncation x₀ = ∣ x₀ ∣₁

𝟘 : Type
𝟘 = ⊥

𝟘-isProp : isProp 𝟘
𝟘-isProp = λ x ()

init-map : (X : Type ℓ) → 𝟘 → X
init-map X ()
-- uninhabEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} →
--   (A → ⊥) → (B → ⊥) → A ≃ B
x→𝟘⇒x≃𝟘 : (X → 𝟘) → X ≃ 𝟘
x→𝟘⇒x≃𝟘 f = uninhabEquiv f (init-map 𝟘)

∥𝟘∥₁≃𝟘 : ∥ 𝟘 ∥₁ ≃ 𝟘
∥𝟘∥₁≃𝟘 = propTruncIdempotent≃ 𝟘-isProp

x→𝟘⇒∥X∥₁≃𝟘 : {X : Type} → (X → 𝟘) → ∥ X ∥₁ ≃ 𝟘
x→𝟘⇒∥X∥₁≃𝟘 {X = X} f = subst (λ x → ∥ x ∥₁ ≃ 𝟘) 𝟘≡X ∥𝟘∥₁≃𝟘
  where
  𝟘≡X : 𝟘 ≡ X
  𝟘≡X = sym (ua (x→𝟘⇒x≃𝟘 f))

-- Nicolai Kraus lemma
Kraus-lemma : (f : X → X) → (2-Constant f)
  → isProp (Fixpoint f)
Kraus-lemma {X = X} f fconst (x , p) (y , q) i =
  s i , t i
  where
  noose : ∀ x y → f x ≡ f y
  noose x y = sym (fconst x x) ∙ fconst x y
  -- the main idea is that for any path p, cong f p does not depend on p
  -- but only on its endpoints and the structure of 2-Constant f
  KrausInsight : ∀ {x y} → (p : x ≡ y) → noose x y ≡ congS f p
  KrausInsight {x} = J (λ y p → noose x y ≡ congS f p) (lCancel (fconst x x))
  -- Need to solve for a path s : x ≡ y, such that:
  -- transport (λ i → congS f s i ≡ s i) p ≡ q
  s : x ≡ y
  s = sym p ∙∙ noose x y ∙∙ q
  t' : PathP (λ i → noose x y i ≡ s i) p q
  t' i j = doubleCompPath-filler (sym p) (noose x y) q j i
  t : PathP (λ i → congS f s i ≡ s i) p q
  t = subst (λ kraus → PathP (λ i → kraus i ≡ s i) p q) (KrausInsight s) t'
