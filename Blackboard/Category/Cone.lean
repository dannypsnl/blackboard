import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Basic

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

structure Cone (F : C ⥤ D) where
  obj : D
  ρ : ∀ c : C, obj ⟶ F.obj c
  eq : ∀ {x y : C}, ∀ f : x ⟶ y, ρ x ≫ F.map f = ρ y

structure Limit (F : C ⥤ D) extends Cone F where
  condition : ∀ c : Cone F, ∃! m : c.obj ⟶ obj, ∀ x : C, c.ρ x = m ≫ ρ x

noncomputable def limit_unique
  (F : C ⥤ D)
  (L1 L2 : Limit F)
  : L1.obj ≅ L2.obj := by
  have c1 := L1.condition L2.toCone
  have c2 := L2.condition L1.toCone
  have s1 := c1.exists.choose_spec
  have s2 := c2.exists.choose_spec
  exact {
    hom := c2.exists.choose
    inv := c1.exists.choose
    inv_hom_id := by
      have another : ∀ x : C, L2.ρ x = (c1.exists.choose ≫ c2.exists.choose) ≫ L2.ρ x := by
        intro X
        have := s1 X
        rw [s2 X] at this
        rw [assoc]
        exact this
      have self := L2.condition L2.toCone
      have : ∀ x : C, L2.ρ x = 𝟙 _ ≫ L2.ρ x := by simp
      have uniq := self.unique another this
      exact uniq
    hom_inv_id := by
      have another : ∀ x : C, L1.ρ x = (c2.exists.choose ≫ c1.exists.choose) ≫ L1.ρ x := by
        intro X
        have := s2 X
        rw [s1 X] at this
        rw [assoc]
        exact this
      have self := L1.condition L1.toCone
      have : ∀ x : C, L1.ρ x = 𝟙 _ ≫ L1.ρ x := by simp
      have uniq := self.unique another this
      exact uniq
  }

theorem limit_unique'
  (F : C ⥤ D)
  (L : Limit F)
  (f g : M ⟶ L.obj)
  : (∀ X : C, f ≫ L.ρ X = g ≫ L.ρ X) → f = g := by
  intros H
  let F_cone : Cone F := {
    obj := M
    ρ c := f ≫ L.ρ c
    eq := by
      intros x y k
      rw [assoc]
      rw [L.eq k]
  }
  have F_over := L.condition F_cone
  have fs := F_over.exists.choose_spec
  unfold F_cone at fs
  simp at fs
  have ok : ∀ x : C, f ≫ L.ρ x = f ≫ L.ρ x := by
    exact fun x ↦ rfl
  have f_factor := F_over.unique ok fs
  have g_factor := F_over.unique H fs
  rw [g_factor]
  exact f_factor
