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

def functor_preserves_isomorphism
  (F : C ⥤ D)
  (X Y : C)
  (iso : X ≅ Y)
  : F.obj X ≅ F.obj Y := {
  hom := F.map iso.hom
  inv := F.map iso.inv
}

noncomputable def fully_faithful_functor_reflects_isomorphism
  (F : C ⥤ D)
  [Functor.Full F]
  [Functor.Faithful F]
  (X Y : C)
  (iso : F.obj X ≅ F.obj Y)
  : X ≅ Y := {
  hom := F.preimage iso.hom
  inv := F.preimage iso.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)
}

def retraction_is_mono_is_necessarily_an_isomorphism
  (X Y : C)
  (f : X ⟶ Y)
  (s : SplitMono f)
  (m : Mono s.retraction)
  : X ≅ Y := {
  hom := f
  inv := s.retraction
  hom_inv_id := s.id
  inv_hom_id := by
    have : s.retraction ≫ f ≫ s.retraction = s.retraction ≫ 𝟙 X :=
      whisker_eq s.retraction s.id
    have : s.retraction ≫ f ≫ s.retraction = 𝟙 Y ≫ s.retraction := by
      simp
    rw [←assoc] at this
    have := m.right_cancellation _ _ this
    exact this
}
