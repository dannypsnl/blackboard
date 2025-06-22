open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool

module basic.bool-eq where

𝟚 = Bool

_==_ : 𝟚 → 𝟚 → 𝟚
true == true = true
false == false = true
a == b = false

eq-bool : (a b : 𝟚) → a ≡ b → a == b ≡ true
eq-bool false false H = refl
eq-bool false true H = H
eq-bool true false H = sym H
eq-bool true true H = H
