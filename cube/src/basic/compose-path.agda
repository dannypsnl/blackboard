open import Cubical.Foundations.Prelude

module basic.compose-path where

variable
  ℓ : Level
  A : Type ℓ
  x y z : A

compPath : x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ{ j (i = i0) → x
                                 ; j (i = i1) → q j })
                               (p i)
