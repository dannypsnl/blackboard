open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Functions.Fixpoint
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Empty using (⊥) renaming (rec to recEmpty)

module computability.rice where

variable
  ℓ : Level
  A : Type ℓ

byAbsurdity : {Anything : Type ℓ} → ⊥ → Anything
byAbsurdity x = recEmpty x

𝟚 = Bool

_==_ : 𝟚 → 𝟚 → 𝟚
true == true = true
false == false = true
a == b = false

not-eq-bool : (a b : 𝟚) → (¬ a ≡ b) → a == b ≡ false
not-eq-bool false true H = refl
not-eq-bool true false H = refl
not-eq-bool false false H = byAbsurdity (H refl)
not-eq-bool true true H = byAbsurdity (H refl)

eq-bool : (a b : 𝟚) → a ≡ b → a == b ≡ true
eq-bool false false H = refl
eq-bool false true H = H
eq-bool true false H = sym H
eq-bool true true H = H

module _ (fA : (e : A → A) → Fixpoint e) (f : A → 𝟚) (x y : A) where
  g : A → A
  g z = if f z == f y then x else y
  u : A
  u = fixpoint (fA g)

  gu≡u : g u ≡ u
  gu≡u = fixpointPath (fA g)

  rice : f x ≡ f y
  rice with f u ≟ f y
  ...| yes P = f x ≡⟨ sym (congS f u≡x) ⟩
               f u ≡⟨ P ⟩
               f y ∎
    where
    u≡x : u ≡ x
    u≡x =
      u ≡⟨ sym gu≡u ⟩
      g u ≡⟨ refl ⟩
      (if f u == f y then x else y) ≡⟨ cong (λ b → if b then x else y) (eq-bool (f u) (f y) P) ⟩
      (if true then x else y) ≡⟨ refl ⟩
      x ∎
  ...| no P = f x ≡⟨ sym (congS f u≡x) ⟩
              f u ≡⟨ l' ⟩
              f y ∎
    where
    noteq : f u == f y ≡ false
    noteq = not-eq-bool (f u) (f y) P
    l : u ≡ y
    l =
      u ≡⟨ sym (fA g .snd) ⟩
      g u ≡⟨ refl ⟩
      (if f u == f y then x else y) ≡⟨ cong (λ b → if b then x else y) noteq ⟩
      (if false then x else y) ≡⟨ refl ⟩
      y ∎
    l' : f u ≡ f y
    l' = congS f l
    u≡x : u ≡ x
    u≡x =
      u ≡⟨ sym gu≡u ⟩
      g u ≡⟨ refl ⟩
      (if f u == f y then x else y) ≡⟨ cong (λ b → if b then x else y) (eq-bool (f u) (f y) l') ⟩
      (if true then x else y) ≡⟨ refl ⟩
      x ∎
