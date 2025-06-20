import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

def left_adjoint_preserves_initial
  (I : C)
  (isI : Limits.IsInitial I)
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  : ∀ X : D, Unique ((F.obj I) ⟶ X) := by
  intros X
  let f := F.map (isI.to (G.obj X))
  exact {
    default := f ≫ adj.counit.app X
    uniq := by
      intros g
      refine (Adjunction.unit_comp_map_eq_iff adj g (isI.to (G.obj X))).mp ?_
      exact Eq.symm (Limits.IsInitial.hom_ext isI (isI.to (G.obj X)) (adj.unit.app I ≫ G.map g))
  }

def left_adjoint_preserves_initial'
  (I : C)
  (isI : Limits.IsInitial I)
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  : Limits.IsInitial (F.obj I) := by
  have H : (Y : D) → Unique ((F.obj I) ⟶ Y) := by
    exact fun Y ↦ left_adjoint_preserves_initial I isI F G adj Y
  exact Limits.IsInitial.ofUnique (F.obj I)
