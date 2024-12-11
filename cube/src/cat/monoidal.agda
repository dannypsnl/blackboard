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
  strict-prop : (b c : ob) → (b ⊗ c) ⊗ unit ≡ b ⊗ (c ⊗ unit)
  strict-prop b c = sym (assoc b c unit)

module _ {ℓ ℓ' : Level} {V : MonoidalCategory ℓ ℓ'} where
  open MonoidalCategory V

  prop : (b c : ob) → α⟨ unit , b , c ⟩ ⋆ η⟨ b ⟩ ⊗ₕ id ≡ η⟨ b ⊗ c ⟩
  prop b c = {!   !}
