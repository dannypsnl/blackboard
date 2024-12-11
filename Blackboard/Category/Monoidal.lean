import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category

open CategoryTheory

variable
  {𝕮 : Type u}
  [Category.{v, u} 𝕮]
  [MonoidalCategory.{v, u} 𝕮]

infixr:81 " ◁ " => MonoidalCategoryStruct.whiskerLeft
infixl:81 " ▷ " => MonoidalCategoryStruct.whiskerRight
infixr:70 " ⊗ " => MonoidalCategoryStruct.tensorObj
notation "𝟙_ " C:max => (MonoidalCategoryStruct.tensorUnit : C)
notation "α_" => MonoidalCategoryStruct.associator
notation "λ_" => MonoidalCategoryStruct.leftUnitor
notation "ρ_" => MonoidalCategoryStruct.rightUnitor

def a (A B C : 𝕮) : A ⊗ (B ⊗ C) ≅ (A ⊗ B) ⊗ C
  := by
  exact (MonoidalCategory.associator A B C).symm

def pentagon_unit_unit (B C : 𝕮)
  : (α_ (𝟙_ 𝕮) (𝟙_ 𝕮) B).hom ▷ C ≫ (α_ (𝟙_ 𝕮) ((𝟙_ 𝕮) ⊗ B) C).hom ≫ (𝟙_ 𝕮) ◁ (α_ (𝟙_ 𝕮) B C).hom
  = (α_ ((𝟙_ 𝕮) ⊗ (𝟙_ 𝕮)) B C).hom ≫ (α_ (𝟙_ 𝕮) (𝟙_ 𝕮) (B ⊗ C)).hom
  := MonoidalCategory.pentagon (𝟙_ 𝕮) (𝟙_ 𝕮) B C
