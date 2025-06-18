import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.FullyFaithful

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

structure IsInverse {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) where
  left : f ≫ g = 𝟙 X
  right : g ≫ f = 𝟙 Y

theorem inverse_is_unique
  (Y : C)
  (f : X ⟶ Y)
  (g k : Y ⟶ X)
  (Hg : IsInverse f g)
  (Hk : IsInverse f k)
  : g = k := by
  have A := Hg.right =≫ k
  have B := Hk.right =≫ k
  rw [←B] at A
  simp [assoc] at A
  rw [Hk.left] at A
  simp [comp_id] at A
  exact A

-- This is a construction proof
-- `X ≅ Y` is `Iso X Y`
def functor_preserves_isomorphism
  (F : C ⥤ D)
  (X Y : C)
  (iso : X ≅ Y)
  : F.obj X ≅ F.obj Y := {
    hom := F.map iso.hom
    inv := F.map iso.inv
    hom_inv_id := by
      have fact := iso.hom_inv_id
      rw [←F.map_comp, ←F.map_id]
      exact congrArg F.map fact
    inv_hom_id := by
      have fact := iso.inv_hom_id
      rw [←F.map_comp, ←F.map_id]
      exact congrArg F.map fact
  }

def nat_iso_from_every_obj_is_isomorphic
  (F G : C ⥤ D)
  (H : (X : C) → F.obj X ≅ G.obj X)
  : F ≅ G := {
    hom := {
      app X := (H X).hom
      naturality X Y f := by
        have Hy_iso := H Y
        have Hx_iso := H X
        have A := Hy_iso.hom_inv_id
        have B := Hy_iso.inv_hom_id
        sorry
    }
    inv := {
      app X := (H X).inv
      naturality X Y f := by
        have Hy_iso := H Y
        sorry
    }
    hom_inv_id := by
      refine (inv_comp_eq_id (𝟙 F)).mp ?_
      simp
      sorry
    inv_hom_id := by
      sorry
  }
