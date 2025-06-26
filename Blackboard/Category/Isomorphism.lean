import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Data.Set.Image

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

theorem id_is_isomorphism
  (X : C)
  : IsIso (𝟙 X) := ⟨ 𝟙 X, by rw [id_comp]; exact Prod.mk_inj.mp rfl ⟩

def compose_iso_is_iso
  (X Y Z : C)
  (iso1 : X ≅ Y)
  (iso2 : Y ≅ Z)
  : X ≅ Z := {
    hom := iso1.hom ≫ iso2.hom
    inv := iso2.inv ≫ iso1.inv
    hom_inv_id := by
      rw [assoc]
      rw [←assoc (iso2.hom)]
      rw [iso2.hom_inv_id]
      rw [id_comp]
      rw [iso1.hom_inv_id]
    inv_hom_id := by
      rw [assoc]
      rw [←assoc (iso1.inv)]
      rw [iso1.inv_hom_id]
      rw [id_comp]
      rw [iso2.inv_hom_id]
  }

theorem iso_is_mono
  (X Y : C)
  (iso : X ≅ Y)
  : Mono iso.hom := {
  right_cancellation {Z} g h := by
    rw [←iso.comp_inv_eq]
    rw [assoc]
    rw [iso.hom_inv_id]
    rw [comp_id]
    exact fun a ↦ a
}

theorem iso_is_epi
  (X Y : C)
  (iso : X ≅ Y)
  : Epi iso.hom := {
  left_cancellation {Z} g h := by
    rw [←iso.inv_comp_eq]
    rw [←assoc]
    rw [iso.inv_hom_id]
    rw [id_comp]
    exact fun a ↦ a
}
