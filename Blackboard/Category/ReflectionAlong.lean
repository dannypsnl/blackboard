import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatTrans

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

noncomputable def each_object_a_reflection_along_F_induces_functor_and_natural_transformation
  (F : C ⥤ D)
  (ReflectionOf : ∀ B : D, Reflection B F)
  : Σ R : D ⥤ C, NatTrans (Functor.id D) (R ⋙ F) := {
    fst := {
      obj X := (ReflectionOf X).R
      map {X Y} f := by
        let ηX := (ReflectionOf X).ηβ
        let ηY := (ReflectionOf Y).ηβ
        let b := f ≫ ηY
        have uniq := (ReflectionOf X).equation (ReflectionOf Y).R b
        exact uniq.choose
      map_id X := by
        let b := 𝟙 X ≫ (ReflectionOf X).ηβ
        have uniq := (ReflectionOf X).equation (ReflectionOf X).R b
        have h1 : (ReflectionOf X).ηβ ≫ F.map uniq.choose = b := uniq.choose_spec.1
        have h2 : (ReflectionOf X).ηβ ≫ F.map (𝟙 (ReflectionOf X).R) = b := by simp [b]
        exact uniq.unique h1 h2
      map_comp {X Y Z} f g := by
        let b := (f ≫ g) ≫ (ReflectionOf Z).ηβ
        have uniq := (ReflectionOf X).equation (ReflectionOf Z).R b
        have h1 : (ReflectionOf X).ηβ ≫ F.map uniq.choose = b := uniq.choose_spec.1

        let b1 := f ≫ (ReflectionOf Y).ηβ
        let b2 := g ≫ (ReflectionOf Z).ηβ
        have uniq1 := (ReflectionOf X).equation (ReflectionOf Y).R b1
        have uniq2 := (ReflectionOf Y).equation (ReflectionOf Z).R b2

        have h2 : (ReflectionOf X).ηβ ≫ F.map (uniq1.choose ≫ uniq2.choose) = b := by
          rw [F.map_comp]
          rw [←assoc, uniq1.choose_spec.1]
          simp [b1]
          rw [uniq2.choose_spec.1]
          simp [b, b2]

        exact uniq.unique h1 h2
    }
    snd := {
      app X := (ReflectionOf X).ηβ
      naturality := by
        intros X Y f
        simp [Functor.id_map, Functor.comp_map]
        let b := f ≫ (ReflectionOf Y).ηβ
        have uniq := (ReflectionOf X).equation (ReflectionOf Y).R b
        exact uniq.choose_spec.1.symm
    }
  }
