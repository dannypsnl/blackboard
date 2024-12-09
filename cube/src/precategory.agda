open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

module precategory where

record Precategory (o h : Level) : Type (ℓ-suc (ℓ-max o h)) where
  no-eta-equality
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
  field
    Hom-set : (x y : Ob) → isSet (Hom x y)
  field
    id : ∀ {x} → Hom x x
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
  infixr 40 _∘_
  field
    idr : ∀ {x y} (f : Hom x y) → f ∘ id ≡ f
    idl : ∀ {x y} (f : Hom x y) → id ∘ f ≡ f
    assoc : ∀ {w x y z} (f : Hom y z) (g : Hom x y) (h : Hom w x)
          → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
