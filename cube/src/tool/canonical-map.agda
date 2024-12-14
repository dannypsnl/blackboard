module tool.canonical-map where

open import Cubical.Foundations.Prelude

record Canonical-Map {ℓ ℓ' : Level} (X : Type ℓ) (Y : Type ℓ')
  : Type (ℓ-max ℓ ℓ') where
  field
    ι : X → Y

open Canonical-Map {{...}} public

variable
  ℓ ℓ' : Level

canonical-map : (X : Type ℓ) (Y : Type ℓ') → {{_ : Canonical-Map X Y}} → X → Y
canonical-map X Y = ι

[_] : {X : Type ℓ} {Y : Type ℓ'} {{ r : Canonical-Map X Y }} → X → Y
[_] = ι

private module _ where
  open import Cubical.Data.Bool
  open import Cubical.Data.Nat

  toℕ : Bool → ℕ
  toℕ true = 1
  toℕ false = 0

  instance
    canonical-map-Bool-to-ℕ : Canonical-Map Bool ℕ
    ι {{canonical-map-Bool-to-ℕ}} = toℕ

  test : ι true ≡ 1
  test = refl
