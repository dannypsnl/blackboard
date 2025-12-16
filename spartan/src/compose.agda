module compose where

open import MLTT.Spartan hiding (_∘_)

variable
  A B C D : 𝓤 ̇

_∘_ : (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

main : ∀ (h : C → D) (g : B → C) (f : A → B) → h ∘ (g ∘ f) ＝ (h ∘ g) ∘ f
main h g f =
  h ∘ (g ∘ f)                   ＝⟨by-definition⟩
  h ∘ (λ x → g (f x))           ＝⟨by-definition⟩
  (λ x → h ((λ x → g (f x)) x)) ＝⟨by-definition⟩
  (λ x → h (g (f x)))           ＝⟨by-definition⟩
  (λ x → (λ z → h (g z)) (f x)) ＝⟨by-definition⟩
  (λ x → (h ∘ g) (f x))         ＝⟨by-definition⟩
  (h ∘ g) ∘ f ∎
