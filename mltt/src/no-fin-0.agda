module no-fin-0 where

-- https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/
open import Agda.Primitive renaming (Set to Type; Setω to Typeω)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data ⊥ : Type where

data Fin : Nat → Type where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

fin-elim : (C : (n : Nat) → Fin n → Type)
           → (∀ n → C (suc n) fz)
           → (∀ n (f : Fin n) → C n f → C (suc n) (fs f))
           → (n : Nat) (f : Fin n) → C n f
fin-elim C cz cs (suc n) fz = cz n
fin-elim C cz cs (suc n) (fs f) = cs n f (fin-elim C cz cs n f)

-- To prove no inhabitants of Fin 0 using the eliminator,
-- we need to use a “large elimination” (a type computed by recursion on a term):
main : Fin 0 → ⊥
main = fin-elim Pred (λ n → tt) (λ n f _ → tt) 0
  where
  Pred : (n : Nat) → Fin n → Type
  Pred 0 f = ⊥
  Pred (suc _) _ = ⊤

-- A related idea: in MLTT without a universe, cannot prove that the successor function is injective, because to do so we need a large elimination.

-- Dependent pattern matching in Agda, effectively gives us the K-like elimination rules for each inductive family.
-- Hence we can prove like below
agda : Fin 0 → ⊥
agda ()
