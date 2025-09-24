open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Int

module basic.pos-or-neg where

data Sign : Type where
  positive negative : Sign

pos-or-neg : Sign → Type
pos-or-neg positive = ℕ
pos-or-neg negative = ℤ

pos-or-neg-three : (s : Sign) → pos-or-neg s
pos-or-neg-three positive = 3
pos-or-neg-three negative = -3
