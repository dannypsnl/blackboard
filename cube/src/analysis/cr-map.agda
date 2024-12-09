open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; zero)
open import Cubical.Data.Nat.Properties using (max; maxComm)

module analysis.cr-map where

data F : Type where
  _+_ _×_ _∘_ : F → F → F
  _𝕕_ : F → ℕ → F
  𝕗 𝕘 : F
infixl 20 _+_
infixl 19 _×_
infixl 18 _∘_

d : F → F
d (f + g) = (d f) + (d g)
d (f × g) = (d f) × g + f × (d g)
d (f ∘ g) = (d f) ∘ g × (d g)
d (x 𝕕 n) = x 𝕕  (suc n)
d 𝕗 = 𝕗 𝕕 1
d 𝕘 = 𝕘 𝕕 1

ex : F
ex = d (𝕗 ∘ 𝕘)

order : F → ℕ
order (f + g) = max (order f) (order g)
order (f × g) = max (order f) (order g)
order (f ∘ g) = max (order f) (order g)
order (f 𝕕 x) = x
order 𝕗 = 0
order 𝕘 = 0

max-suc : (n : ℕ) → suc n ≡ max n (suc n)
max-suc zero = refl
max-suc (suc n) = cong suc (max-suc n)

suc-max : (n : ℕ) → suc n ≡ max (suc n) n
suc-max zero = refl
suc-max (suc n) = cong suc (suc-max n)

max-reduce : (n m : ℕ) → max (suc n) (suc m) ≡ max (max (suc n) (max m n)) (suc m)
max-reduce zero zero = refl
max-reduce zero (suc m) = cong suc (max-suc m)
max-reduce (suc n) zero = cong suc (subst (λ x → suc n ≡ max x 0) (suc-max n) refl)
max-reduce (suc n) (suc m) = cong suc (max-reduce n m)

max-self : (n : ℕ) → n ≡ max n n
max-self zero = refl
max-self (suc n) = cong suc (max-self n)

order[dh]≡order[h]+1 : (h : F) → order (d h) ≡ suc (order h)
order[dh]≡order[h]+1 (f + g) =
  subst2 (λ x y → max x y ≡ suc (order (f + g))) (sym (order[dh]≡order[h]+1 f)) (sym (order[dh]≡order[h]+1 g))
    (cong suc refl)
order[dh]≡order[h]+1 (f × g) =
  subst2 (λ x y → max (max x (max (order g) (order f))) y ≡ suc (order (f × g)))
    (sym (order[dh]≡order[h]+1 f)) (sym (order[dh]≡order[h]+1 g))
    (subst (λ x → x ≡ suc (order (f × g))) (max-reduce (order f) (order g))
      (cong suc refl))
order[dh]≡order[h]+1 (f ∘ g) =
  subst2 (λ x y → max x (max (order g) y) ≡  suc (max (order f) (order g)))
    (sym (order[dh]≡order[h]+1 f))
    (sym (order[dh]≡order[h]+1 g))
    (subst (λ x → max (suc (order f)) x ≡ suc (max (order f) (order g)))
      (max-suc (order g))
      (cong suc refl))
order[dh]≡order[h]+1 (f 𝕕 x) = cong suc refl
order[dh]≡order[h]+1 𝕗 = refl
order[dh]≡order[h]+1 𝕘 = refl
