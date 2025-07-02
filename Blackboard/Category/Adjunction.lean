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

theorem fully_faithful_right_adjoint_implies_counit_isIso
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  (ff : G.FullyFaithful)
  : IsIso adj.counit := by
  refine (NatTrans.isIso_iff_isIso_app adj.counit).mpr ?_
  intros X
  let u := adj.unit.app (G.obj X)
  let pu := ff.preimage u
  let c := adj.counit.app X
  simp at c
  have LTri : F.map u ≫ adj.counit.app (F.obj (G.obj X)) = 𝟙 (F.obj (G.obj X)) :=
    adj.left_triangle_components (G.obj X)
  -- NOTE: unit and left adjoint is defined uniquely up to isomorphism
  have L : c ≫ ff.preimage u = 𝟙 (F.obj (G.obj X)) := by
    sorry

  have back_to_c : ff.preimage (G.map c) = c := ff.preimage_map c
  have RTri : u ≫ (G.map c) = 𝟙 (G.obj X) := adj.right_triangle_components X
  have R : ff.preimage u ≫ c = 𝟙 X := by
    rw [←back_to_c]
    rw [←ff.preimage_comp]
    rw [RTri]
    simp
  have H : c ≫ ff.preimage u = 𝟙 (F.obj (G.obj X)) ∧ ff.preimage u ≫ c = 𝟙 X := by
    exact ⟨ L , R ⟩
  have H : ∃ inv : X ⟶ (F.obj (G.obj X)), c ≫ inv = 𝟙 (F.obj (G.obj X)) ∧ inv ≫ c = 𝟙 X :=
    Exists.intro (ff.preimage u) H
  exact { out := H }
