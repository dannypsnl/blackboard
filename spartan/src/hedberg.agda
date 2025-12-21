{-# OPTIONS --without-K #-}
module hedberg where

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import MLTT.NaturalNumbers
open import UF.Base
open import UF.Sets
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

-- Reading https://planetmath.org/72UniquenessOfIdentityProofsAndHedbergsTheorem
has-decidable-equality : (X : 𝓤 ̇ ) → 𝓤 ̇
has-decidable-equality X = (x y : X) → (x ＝ y) + ¬ (x ＝ y)

thm7-2-1 : (X : 𝓤 ̇ ) → is-set X ↔ ((x : X) → (p : x ＝ x) → p ＝ 𝓻𝓮𝒻𝓵 x)
thm7-2-1 {𝓤} X = L , R
  where
  L : is-set X → ((x : X) → (p : x ＝ x) → p ＝ refl)
  L isSet x p = isSet p refl

  R : ((x : X) → (p : x ＝ x) → p ＝ refl) → is-set X
  R H {x}{y} p q = cancel-right p q (p ⁻¹) III
    where
    I : (p ∙ p ⁻¹) ＝ refl
    I = H x (p ∙ p ⁻¹)
    II = H x (q ∙ p ⁻¹)
    III : p ∙ p ⁻¹ ＝ q ∙ p ⁻¹
    III = (I ∙ II ⁻¹)

postulate fe : funext 𝓤 𝓤₀

collary7-2-3 : (X : 𝓤 ̇ ) → (H : (x y : X) → ¬¬ (x ＝ y) → (x ＝ y)) → is-set X
collary7-2-3 X H {x} {y} p q =
  p                  ＝⟨ lemma p ⟩
  f x refl ⁻¹ ∙ f y p ＝⟨ ap (λ - → f x refl ⁻¹ ∙ -) (f-is-const p q) ⟩
  f x refl ⁻¹ ∙ f y q ＝⟨ lemma q ⁻¹ ⟩
  q ∎
  where
  f : (y : X) → x ＝ y → x ＝ y
  f y p = H x y (¬¬-intro p)

  f-is-const : {y : X} → (p q : x ＝ y) → f y p ＝ f y q
  f-is-const {y} p q = ap (H x y) (Π-is-prop fe (λ _ → 𝟘-is-prop) (¬¬-intro p) (¬¬-intro q))

  lemma : {y : X} (p : x ＝ y) → p ＝ f x refl ⁻¹ ∙ f y p
  lemma refl = sym-is-inverse (f x refl)

Hedberg : (X : 𝓤 ̇ ) → has-decidable-equality X → is-set X
Hedberg X decX = collary7-2-3 X c
  where
  lemma7-2-4 : {A : 𝓤 ̇ } → (A + ¬ A) → (¬¬ A → A)
  lemma7-2-4 = Right-fails-gives-left-holds

  c : (x y : X) → ¬¬(x ＝ y) → (x ＝ y)
  c x y = lemma7-2-4 (decX x y)

-- Theorem 7.2.6
-- The type ℕ of natural numbers has decidable equality, and hence is a set.
thm7-2-6 : is-set ℕ
thm7-2-6 = Hedberg ℕ is-dec
  where
  -- Read https://planetmath.org/213naturalnumbers for encode-decode
  code : ℕ → ℕ → 𝓤₀ ̇
  code 0 0 = 𝟙
  code 0 (succ y) = 𝟘
  code (succ x) 0 = 𝟘
  code (succ x) (succ y) = code x y

  r : (n : ℕ) → code n n
  r 0 = ⋆
  r (succ x) = r x

  encode : (m n : ℕ) → m ＝ n → code m n
  encode m n p = transport (code m) p (r m)

  decode : (m n : ℕ) → code m n → m ＝ n
  decode 0 0 c = refl
  decode (succ m) (succ n) c = ap succ (decode m n c)

  is-dec : has-decidable-equality ℕ
  is-dec 0 0 = inl refl
  is-dec 0 (succ y) = inr (encode 0 (succ y))
  is-dec (succ x) 0 = inr (encode (succ x) 0)
  is-dec (succ x) (succ y) = equality-cases (is-dec x y) pos neg
    where
    pos : (p : x ＝ y) → is-dec x y ＝ inl p → (succ x ＝ succ y) + ¬ (succ x ＝ succ y)
    pos p inl-p = inl (decode (succ x) (succ y) (encode x y p))

    neg : (np : ¬ (x ＝ y)) → is-dec x y ＝ inr np → (succ x ＝ succ y) + ¬ (succ x ＝ succ y)
    neg np inr-np = inr proof
      where
      proof : succ x ＝ succ y → 𝟘
      proof sx=sy = np (decode x y key)
        where
        -- `decode x y ?0` is expecting that `?0 : code x y` there,
        -- but by definition `code x y = code (succ x) (succ y)`,
        -- and that's what we have here!
        key : code (succ x) (succ y)
        key = encode (succ x) (succ y) sx=sy
