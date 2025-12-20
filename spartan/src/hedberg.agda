{-# OPTIONS --without-K #-}
module hedberg where

open import MLTT.Spartan
open import MLTT.Plus-Properties
open import UF.Sets

-- Reading https://planetmath.org/72UniquenessOfIdentityProofsAndHedbergsTheorem
decidable : (X : 𝓤 ̇ ) → 𝓤 ̇
decidable X = (x y : X) → (x ＝ y) + ¬ (x ＝ y)

-- I have no idea how to not rely on this, and not be attacked by transport
∙-assoc : {X : 𝓤 ̇ } → {x y z w : X} → (p : x ＝ y) → (q : y ＝ z) → (r : z ＝ w) → p ∙ q ∙ r ＝ p ∙ (q ∙ r)
∙-assoc refl refl refl = refl

thm7-2-1 : (X : 𝓤 ̇ ) → is-set X ↔ ((x : X) → (p : x ＝ x) → p ＝ 𝓻𝓮𝒻𝓵 x)
thm7-2-1 {𝓤} X = L , R
  where
  L : is-set X → ((x : X) → (p : x ＝ x) → p ＝ refl)
  L isSet x p = isSet p refl

  R : ((x : X) → (p : x ＝ x) → p ＝ refl) → is-set X
  R H {x}{y} p q = p ＝⟨ ∙-agrees-with-∙' p refl ⁻¹ ⟩
                   p ∙' (𝓻𝓮𝒻𝓵 y) ＝⟨ ap (p ∙'_) (H y (p ⁻¹ ∙ p) ⁻¹) ⟩
                   p ∙' ((p ⁻¹) ∙ p) ＝⟨ ∙-agrees-with-∙' p (p ⁻¹ ∙ p) ⟩
                   p ∙ ((p ⁻¹) ∙ p) ＝⟨ ∙-assoc p (p ⁻¹) p ⁻¹ ⟩
                   p ∙ (p ⁻¹) ∙ p ＝⟨ ap (_∙ p) (I ∙ II ⁻¹) ⟩
                   q ∙ (p ⁻¹) ∙ p ＝⟨ ∙-assoc q (p ⁻¹) p ⟩
                   q ∙ ((p ⁻¹) ∙ p) ＝⟨ ∙-agrees-with-∙' q ((p ⁻¹) ∙ p) ⁻¹ ⟩
                   q ∙' ((p ⁻¹) ∙ p) ＝⟨ ap (q ∙'_) (H y (p ⁻¹ ∙ p)) ⟩
                   q ∙' (𝓻𝓮𝒻𝓵 y) ＝⟨ ∙-agrees-with-∙' q refl ⟩
                   q ∎
    where
    I : (p ∙ p ⁻¹) ＝ refl
    I = H x (p ∙ p ⁻¹)
    II = H x (q ∙ p ⁻¹)

