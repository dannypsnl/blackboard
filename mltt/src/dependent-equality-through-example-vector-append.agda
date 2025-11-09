open import Agda.Primitive
  renaming (Set to Type; Setω to Typeω)
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

cong : {X Y : Set} (f : X → Y) {x₀ x₁ : X} → x₀ ≡ x₁ → f x₀ ≡ f x₁
cong {X} {Y} f refl = refl

+-assoc : ∀ l m n → (l + m) + n ≡ l + (m + n)
+-assoc zero     m n = refl
+-assoc (suc l) m n = goal
 where
  IH : (l + m) + n ≡ l + (m + n)
  IH = +-assoc l m n
  goal : suc ((l + m) + n) ≡ suc (l + (m + n))
  goal = cong suc IH

data Vec (A : Type) : Nat → Type where
  [] : Vec A 0
  _::_ : ∀{n} → A → Vec A n → Vec A (suc n)
infixl 40 _::_

_++_ : {Y : Type} {l m : Nat} → (xs : Vec Y l) → (ys : Vec Y m) → Vec Y (l + m)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
infixl 30 _++_

-- Base on a fact to define higher (dependent) equality
_≡[_]_ : {X : Type} {A : X → Type} {x₀ x₁ : X} → A x₀ → x₀ ≡ x₁ → A x₁ → Type
a₀ ≡[ refl ] a₁ = (a₀ ≡ a₁)

module vector-appending-proof where
  -- proposition-does-not-make-sense : (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)

  cong-cons : ∀{X} {m n} (x : X) {xs : Vec X m} {ys : Vec X n} (p : m ≡ n)
          → xs ≡[ p ] ys → x :: xs ≡[ cong suc p ] x :: ys
  cong-cons _ refl refl = refl

  ++-assoc : ∀{X} (l m n : Nat) (xs : Vec X l) (ys : Vec X m) (zs : Vec X n)
           → (xs ++ ys) ++ zs ≡[ +-assoc l m n ] xs ++ (ys ++ zs)
  ++-assoc zero     m n []       ys zs = refl
  ++-assoc (suc l) m n (x :: xs) ys zs = goal
   where
    IH : ((xs ++ ys) ++ zs) ≡[ +-assoc l m n ] (xs ++ (ys ++ zs))
    IH = ++-assoc l m n xs ys zs
    goal : x :: (xs ++ ys) ++ zs ≡[ cong suc (+-assoc l m n) ] x :: (xs ++ (ys ++ zs))
    goal = cong-cons x (+-assoc l m n) IH
