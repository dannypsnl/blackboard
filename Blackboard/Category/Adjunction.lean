import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

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

  let ε := adj.counit.app X
  let η := adj.unit.app (G.obj X)

  have right_triangle : η ≫ G.map ε = 𝟙 (G.obj X) :=
    adj.right_triangle_components X
  have left_triangle : F.map η ≫ adj.counit.app (F.obj (G.obj X)) = 𝟙 (F.obj (G.obj X)) :=
    adj.left_triangle_components (G.obj X)

  let inv := ff.preimage η
  have inv_property : G.map inv = η := ff.map_preimage η

  have L : ε ≫ inv = 𝟙 (F.obj (G.obj X)) := by
    have := adj.counit_naturality inv
    rw [inv_property] at this
    rw [←this]
    exact left_triangle

  have R : inv ≫ ε = 𝟙 X := by
    apply ff.map_injective
    rw [G.map_comp, G.map_id]
    rw [inv_property]
    exact right_triangle

  exact { out := ⟨inv, L, R⟩ }

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit
theorem counit_isIso_implies_fully_faithful_right_adjoint
  (F : C ⥤ D)
  (G : D ⥤ C)
  (adj : F ⊣ G)
  [iso : IsIso adj.counit]
  : G.Full ∧ G.Faithful := {
  left := {
    map_surjective {X Y} f := by
      use (retraction (adj.counit.app X) ≫ (adj.homEquiv (G.obj X) Y).symm f)
      suffices G.map (retraction (adj.counit.app X)) = adj.unit.app (G.obj X) by
        simp [this]
      rw [← id_comp (G.map (retraction (adj.counit.app X)))]
      simp only [
        Functor.id_obj, Functor.comp_obj, id_comp,
        ← adj.right_triangle_components X,
        assoc, ← Functor.map_comp, IsSplitMono.id,
        Functor.map_id, comp_id
      ]
  }
  right := {
    map_injective := by
      intros X Y f g H
      have c1 := adj.counit_naturality f
      have c2 := adj.counit_naturality g
      rw [H] at c1
      rw [c1] at c2
      have e : Epi (adj.counit.app X) := IsIso.epi_of_iso (adj.counit.app X)
      exact (cancel_epi (adj.counit.app X)).mp c2
  }
}
