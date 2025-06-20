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

noncomputable def nat_iso_from_every_obj_is_isomorphic
  (F G : C ⥤ D)
  (τ : NatTrans F G)
  (iso_on_each_object : (X : C) → IsIso (τ.app X))
  : F ≅ G := by
  let H := fun X ↦ asIso (τ.app X)
  have naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (H Y).hom = (H X).hom ≫ G.map f := by
    intros X Y f
    have R (X : C) : (H X).hom = (asIso (τ.app X)).hom := by
      rw [asIso_hom]
    rw [R X, R Y]
    simp
  exact NatIso.ofComponents H naturality

-- LOL, I didn't notice this is exactly how Lean define this
theorem functor_equivalence_condition
  (F : C ⥤ D)
  (ff : F.FullyFaithful)
  (es : F.EssSurj)
  : Functor.IsEquivalence F := by
  exact { faithful := ff.faithful, full := ff.full, essSurj := es }

theorem functor_equivalence_condition'
  (F : C ⥤ D)
  (ff : F.FullyFaithful)
  (es : F.EssSurj)
  : ∃ G : D ⥤ C, ∃ η : NatTrans (G ⋙ F) (𝟭 D), ∀ X : D, IsIso (η.app X) := by
  let G : D ⥤ C := {
    obj d := F.objPreimage d
    map {d1 d2} f := by
      have d1' := (F.objObjPreimageIso d1).hom
      have d2' := (F.objObjPreimageIso d2).inv
      have R := ff.homEquiv (X := F.objPreimage d1) (Y := F.objPreimage d2)
      exact R.invFun (d1' ≫ f ≫ d2')
    map_id X := by simp
    map_comp {X Y Z} f g := by
      simp
      have F_comp := ff.preimage_comp
        (f := (F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
        (g := (F.objObjPreimageIso Y).hom ≫ g ≫ (F.objObjPreimageIso Z).inv)
      rw [F_comp.symm]
      simp
  }
  let η : NatTrans (G ⋙ F) (𝟭 D) := { app d := (F.objObjPreimageIso d).hom }
  have P : ∀ X : D, IsIso (η.app X) := by
    intros X
    let idD_to_GF : (𝟭 D).obj X ⟶ (G ⋙ F).obj X := (F.objObjPreimageIso X).inv
    have R : η.app X ≫ idD_to_GF = 𝟙 ((G ⋙ F).obj X) ∧ idD_to_GF ≫ η.app X = 𝟙 ((𝟭 D).obj X) := by
      unfold η idD_to_GF
      simp
    exact { out := Exists.intro idD_to_GF R }
  exact Exists.intro G (Exists.intro η P)

theorem functor_equivalence_condition''
  (F : C ⥤ D)
  (ff : F.FullyFaithful)
  (es : F.EssSurj)
  : ∃ G : D ⥤ C, ∃ ε : NatTrans (𝟭 C) (F ⋙ G), ∀ X : C, IsIso (ε.app X) := by
  let G : D ⥤ C := {
    obj d := F.objPreimage d
    map {d1 d2} f := by
      have d1' := (F.objObjPreimageIso d1).hom
      have d2' := (F.objObjPreimageIso d2).inv
      have R := ff.homEquiv (X := F.objPreimage d1) (Y := F.objPreimage d2)
      exact R.invFun (d1' ≫ f ≫ d2')
    map_id X := by simp
    map_comp {X Y Z} f g := by
      simp
      have F_comp := ff.preimage_comp
        (f := (F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
        (g := (F.objObjPreimageIso Y).hom ≫ g ≫ (F.objObjPreimageIso Z).inv)
      rw [F_comp.symm]
      simp
  }
  let ε : NatTrans (𝟭 C) (F ⋙ G) := {
    app c := (ff.preimageIso (F.objObjPreimageIso (F.obj c))).inv
    naturality := by
      intro X Y f
      simp_all only [Functor.id_obj, Equiv.invFun_as_coe, Functor.FullyFaithful.homEquiv_symm_apply, Functor.comp_obj,
        Functor.id_map, Functor.FullyFaithful.preimageIso_inv, Functor.comp_map, Functor.FullyFaithful.preimage_comp,
        Functor.FullyFaithful.preimage_map, G]
      exact
        Eq.symm
          (Iso.inv_hom_id_assoc (ff.preimageIso (F.objObjPreimageIso (F.obj X)))
            (f ≫ (ff.preimageIso (F.objObjPreimageIso (F.obj Y))).inv))
  }
  have P : ∀ X : C, IsIso (ε.app X) := by
    intros X
    let FG_to_idC : (F ⋙ G).obj X ⟶ (𝟭 C).obj X :=
      (ff.preimageIso (F.objObjPreimageIso (F.obj X))).hom
    have R : ε.app X ≫ FG_to_idC = 𝟙 ((𝟭 C).obj X) ∧ FG_to_idC ≫ ε.app X = 𝟙 ((F ⋙ G).obj X) := by
      unfold G ε FG_to_idC
      simp
      have F_comp := ff.preimage_comp
        (f := (F.objObjPreimageIso (F.obj X)).hom)
        (g := (F.objObjPreimageIso (F.obj X)).inv)
      rw [←F_comp]
      simp
      rw [←ff.preimageIso_inv (F.objObjPreimageIso (F.obj X))]
      rw [←ff.preimageIso_hom (F.objObjPreimageIso (F.obj X))]
      exact (ff.preimageIso (F.objObjPreimageIso (F.obj X))).inv_hom_id
    exact { out := Exists.intro FG_to_idC R }
  exact Exists.intro G (Exists.intro ε P)
