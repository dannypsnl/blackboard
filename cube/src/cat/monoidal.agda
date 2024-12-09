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

module _ {ℓ ℓ' : Level} {V : MonoidalCategory ℓ ℓ'} where
  open MonoidalCategory V

  prop₁ : (b c : ob) → α⟨ unit , b , c ⟩ ⋆ η⟨ b ⟩ ⊗ₕ id ≡ η⟨ b ⊗ c ⟩
  prop₁ b c =
    let p = pentagon unit unit b c
        t1 = triangle unit (b ⊗ c)
        t2 = triangle unit b
    in {!   !}
