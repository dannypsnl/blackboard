module compose where

open import MLTT.Spartan hiding (_∘_)

variable
  A B C D : 𝓤 ̇
  h : C → D
  g : B → C
  f : A → B

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

main : h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
main = refl
