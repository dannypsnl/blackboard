module cat.monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Monoidal

module _ {ℓ ℓ' : Level} {C : Category ℓ ℓ'} where
  open Category

  involutiveOp' : C ^op ^op ≡ C
  involutiveOp' = refl

  idP' : ∀ {x x'} {p : x ≡ x'} → C [ x , x' ]
  idP' {x} {x'} {p} = subst (λ v → C [ x , v ]) p (C .id)

module _ {ℓ ℓ' : Level} {V : StrictMonCategory ℓ ℓ'} where
  open StrictMonCategory V

  -- strict monoidal category 中可以直接用等式
  prop₁ : (b c : ob) → (b ⊗ c) ⊗ unit ≡ b ⊗ (c ⊗ unit)
  prop₁ b c = sym (assoc b c unit)
