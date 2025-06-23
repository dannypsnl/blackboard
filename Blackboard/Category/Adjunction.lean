import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

def left_adjoint_preserves_initial'
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
def left_adjoint_preserves_initial
  (I : C)
  (isI : Limits.IsInitial I)
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  : Limits.IsInitial (F.obj I) := by
  have H : (Y : D) → Unique ((F.obj I) ⟶ Y) :=
    left_adjoint_preserves_initial' I isI F G adj
  exact Limits.IsInitial.ofUnique (F.obj I)

def right_adjoint_preserves_terminal'
  (T : D)
  (isT : Limits.IsTerminal T)
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  : ∀ X : C, Unique (X ⟶ (G.obj T)) := by
  intros X
  let f := G.map (isT.from (F.obj X))
  exact {
    default : X ⟶ G.obj T := adj.unit.app X ≫ f
    uniq := by
      intros g
      refine (Adjunction.eq_unit_comp_map_iff adj (isT.from (F.obj X)) g).mpr ?_
      exact
        Eq.symm (Limits.IsTerminal.hom_ext isT (isT.from (F.obj X)) (F.map g ≫ adj.counit.app T))
  }
def right_adjoint_preserves_terminal
  (T : D)
  (isT : Limits.IsTerminal T)
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  : Limits.IsTerminal (G.obj T) := by
  have H : (Y : C) → Unique (Y ⟶ (G.obj T)) :=
    right_adjoint_preserves_terminal' T isT F G adj
  exact Limits.IsTerminal.ofUnique (G.obj T)

theorem right_adjoint_is_fully_faithful
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  (ff : G.FullyFaithful)
  : IsIso adj.counit := by
  refine (NatTrans.isIso_iff_isIso_app adj.counit).mpr ?_
  sorry
