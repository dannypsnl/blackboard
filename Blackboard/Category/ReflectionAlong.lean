import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

structure Reflection (B : D) (F : CategoryTheory.Functor C D)  where
  R : C
  ηβ : B ⟶ F.obj R
  equation : (A : C) → (b : B ⟶ F.obj A) → ∃! (α : R ⟶ A), ηβ ≫ F.map α = b

noncomputable def the_reflection
  (F : C ⥤ D)
  (B : D)
  (R1 : Reflection B F)
  (R2 : Reflection B F)
  : R1.R ≅ R2.R := by
  have one := R1.equation R2.R R2.ηβ
  have two := R2.equation R1.R R1.ηβ
  let a1 := one.exists.choose
  let a2 := two.exists.choose
  have P1 : R1.ηβ ≫ F.map a1 = R2.ηβ := one.exists.choose_spec
  have P2 : R2.ηβ ≫ F.map a2 = R1.ηβ := two.exists.choose_spec
  exact {
    hom := a1
    inv := a2
    hom_inv_id := by
      have h1 : R1.ηβ ≫ F.map (a1 ≫ a2) = R1.ηβ := by
        rw [F.map_comp]
        rw [←assoc, P1, P2]
      have h2 : R1.ηβ ≫ F.map (𝟙 R1.R) = R1.ηβ := by simp
      have uniq := R1.equation R1.R R1.ηβ
      exact uniq.unique h1 h2
    inv_hom_id := by
      have h1 : R2.ηβ ≫ F.map (a2 ≫ a1) = R2.ηβ := by
        rw [F.map_comp]
        rw [←assoc, P2, P1]
      have h2 : R2.ηβ ≫ F.map (𝟙 R2.R) = R2.ηβ := by simp
      have uniq := R2.equation R2.R R2.ηβ
      exact uniq.unique h1 h2
  }
