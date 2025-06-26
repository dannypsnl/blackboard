open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism

module cat.isomorphism where

variable
  ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} where
  open Category
  open isIso

  id-is-iso : {x : C .ob} → isIso C {x} {x} (C .id)
  id-is-iso .inv = (C .id)
  id-is-iso .sec =
    _ ⋆⟨ C ⟩ (C .id) ≡⟨ C .⋆IdR (id-is-iso .inv) ⟩
    _ ≡⟨ refl ⟩
    (C .id) ∎
  id-is-iso .ret =
    (C .id) ⋆⟨ C ⟩ (id-is-iso .inv) ≡⟨ C .⋆IdL (id-is-iso .inv) ⟩
    (id-is-iso .inv) ≡⟨ refl ⟩
    (C .id) ∎
