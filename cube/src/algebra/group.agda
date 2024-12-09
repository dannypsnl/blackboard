module algebra.group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Group

variable
  ℓ : Level
  G : Type ℓ

module _ (G : Group ℓ) where
  open GroupStr (snd G)

  abstract
    ·CancelL : (a : ⟨ G ⟩) {b c : ⟨ G ⟩} → a · b ≡ a · c → b ≡ c
    ·CancelL a {b} {c} p =
      b ≡⟨ sym (·IdL b) ∙ congL _·_ (sym (·InvL a)) ∙ sym (·Assoc _ _ _) ⟩
      inv a · a · b ≡⟨ congR _·_ p ⟩
      inv a · a · c ≡⟨ ·Assoc _ _ _ ∙ congL _·_ (·InvL a) ∙ ·IdL c ⟩
      c ∎

    ·CancelR : {a b : ⟨ G ⟩} (c : ⟨ G ⟩) → a · c ≡ b · c → a ≡ b
    ·CancelR {a} {b} c p =
      a ≡⟨ sym (·IdR a) ⟩
      a · 1g ≡⟨ congR _·_ (sym (·InvR c)) ⟩
      a · c · inv c ≡⟨ ·Assoc a c (inv c) ⟩
      (a · c) · inv c ≡⟨ congL _·_ p ⟩
      (b · c) · inv c ≡⟨ sym (·Assoc b c (inv c)) ⟩
      b · c · inv c ≡⟨ congR _·_ (·InvR c) ⟩
      b · 1g ≡⟨ ·IdR b ⟩
      b ∎

    invInv : (a : ⟨ G ⟩) → inv (inv a) ≡ a
    invInv a = ·CancelL (inv a) (·InvR (inv a) ∙  sym (·InvL a))

    idFromIdempotency : (x : ⟨ G ⟩) → x ≡ x · x → x ≡ 1g
    idFromIdempotency x p =
      x                 ≡⟨ sym (·IdR x) ⟩
      x · 1g            ≡⟨ congR _·_ (sym (·InvR x)) ⟩
      x · (x · inv x)   ≡⟨ ·Assoc x x (inv x) ⟩
      (x · x) · (inv x) ≡⟨ congL _·_ (sym p) ⟩
      x · (inv x)       ≡⟨ ·InvR x ⟩
      1g              ∎
