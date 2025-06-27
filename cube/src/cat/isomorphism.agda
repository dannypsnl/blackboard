open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Morphism
open import Cubical.Categories.Isomorphism

module cat.isomorphism where

variable
  ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} where
  open Category
  open isIso

  variable
    x y z : C .ob

  id-is-iso : isIso C {x} {x} (C .id)
  id-is-iso .inv = (C .id)
  id-is-iso .sec =
    _ ⋆⟨ C ⟩ (C .id) ≡⟨ C .⋆IdR (id-is-iso .inv) ⟩
    _ ≡⟨ refl ⟩
    (C .id) ∎
  id-is-iso .ret =
    (C .id) ⋆⟨ C ⟩ (id-is-iso .inv) ≡⟨ C .⋆IdL (id-is-iso .inv) ⟩
    (id-is-iso .inv) ≡⟨ refl ⟩
    (C .id) ∎

  iso-is-monic : (f : C [ x , y ]) → isIso C f → isMonic C f
  iso-is-monic f f-is-iso {z} {a} {b} H =
      a ≡⟨ sym (⋆IdR C a) ⟩
      a ⋆⟨ C ⟩ (C .id) ≡⟨ congS (λ p → a ⋆⟨ C ⟩ p) (sym (f-is-iso .ret)) ⟩
      a ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (f-is-iso .inv)) ≡⟨ sym (⋆Assoc C a f (f-is-iso .inv)) ⟩
      a ⋆⟨ C ⟩ f ⋆⟨ C ⟩ (f-is-iso .inv) ≡⟨ congS (λ v → v ⋆⟨ C ⟩ (f-is-iso .inv)) H ⟩
      b ⋆⟨ C ⟩ f ⋆⟨ C ⟩ (f-is-iso .inv) ≡⟨ ⋆Assoc C b f (f-is-iso .inv) ⟩
      b ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (f-is-iso .inv)) ≡⟨ congS (λ p → b ⋆⟨ C ⟩ p) (f-is-iso .ret) ⟩
      b ⋆⟨ C ⟩ (C .id) ≡⟨ C .⋆IdR b ⟩
      b ∎

  iso-is-epic : (f : C [ x , y ]) → isIso C f → isEpic C f
  iso-is-epic f f-is-iso {z} {a} {b} H =
      a ≡⟨ sym (⋆IdL C a) ⟩
      (C .id) ⋆⟨ C ⟩ a ≡⟨ congS (λ p → p ⋆⟨ C ⟩ a) (sym (f-is-iso .sec)) ⟩
      ((f-is-iso .inv) ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ a ≡⟨ ⋆Assoc C (f-is-iso .inv) f a ⟩
      (f-is-iso .inv) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ a) ≡⟨ congS (λ v → (f-is-iso .inv) ⋆⟨ C ⟩ v) H ⟩
      (f-is-iso .inv) ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ b) ≡⟨ sym (⋆Assoc C (f-is-iso .inv) f b) ⟩
      ((f-is-iso .inv) ⋆⟨ C ⟩ f) ⋆⟨ C ⟩ b ≡⟨ congS (λ p → p ⋆⟨ C ⟩ b) (f-is-iso .sec) ⟩
      (C .id) ⋆⟨ C ⟩ b ≡⟨ C .⋆IdL b ⟩
      b ∎
