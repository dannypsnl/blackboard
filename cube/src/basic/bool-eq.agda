open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool

module basic.bool-eq where

variable
  ℓ : Level

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

ifT : {A : Type ℓ} (c d : A) → A
ifT c d = if true then c else d

l : ifT 1 2 ≡ 1
l = refl

if_eq : {A : Type ℓ} (a b : 𝟚) (c d : A) → A
if_eq a b c d = if a == b then c else d

l2 : if_eq true true 1 2 ≡ 1
l2 = refl
l3 : if_eq true false 1 2 ≡ 2
l3 = refl
