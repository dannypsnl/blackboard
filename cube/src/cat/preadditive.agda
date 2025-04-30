module cat.preadditive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Additive.Base

private
  variable
    ℓ ℓ' : Level

module _ {C : PreaddCategory ℓ ℓ'} where
  open PreaddCategory C

  module _ {x y x×y : ob}
           (π₁ : Hom[ x×y , x ])
           (π₂ : Hom[ x×y , y ]) where

    isProduct : Type (ℓ-max ℓ ℓ')
    isProduct = ∀ (z : ob) (f₁ : Hom[ z , x ]) (f₂ : Hom[ z , y ]) →
        ∃![ f ∈ Hom[ z , x×y ] ] (f ⋆ π₁ ≡ f₁) × (f ⋆ π₂ ≡ f₂)

  module _ (A B P : ob) (pA : Hom[ P , A ]) (pB : Hom[ P , B ]) where
    sA : Hom[ A , P ]
    sA = {!   !}
    sB : Hom[ B , P ]
    sB = {!   !}
