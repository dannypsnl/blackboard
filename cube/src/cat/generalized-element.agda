open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category

module cat.generalized-element where

variable
  ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} where
  open Category

  variable
    X Y : C .ob
  
  forward : {f g : C [ X , Y ]} → f ≡ g → ({S : C .ob} (x : C [ S , X ]) → x ⋆⟨ C ⟩ f ≡ x ⋆⟨ C ⟩ g)
  forward f≡g = λ x → cong (λ a → x ⋆⟨ C ⟩ a) f≡g
  backward : (f g : C [ X , Y ]) → ({S : C .ob} (x : C [ S , X ]) → x ⋆⟨ C ⟩ f ≡ x ⋆⟨ C ⟩ g) → f ≡ g
  backward f g P = f ≡⟨ sym (C .⋆IdL f) ⟩
                   (C .id) ⋆⟨ C ⟩ f ≡⟨ P (C .id) ⟩
                   (C .id) ⋆⟨ C ⟩ g ≡⟨ C .⋆IdL g ⟩
                   g ∎
