import Mathlib.Topology.Basic
import Mathlib.Topology.Maps
import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Order

open Topology

variable
  (X : Type u1)
  [TopologicalSpace X]
  (Y : Type u2)
  [TopologicalSpace Y]
  (Z : Type u3)
  [TopologicalSpace Z]
  (U V W : Set X)

-- NOTE: of course, it's unusal to "prove" this. Since in axiomatized topology, this is an axiom.
theorem union_of_opens_is_open
  (U_is_open : IsOpen U)
  (V_is_open : IsOpen V)
  : IsOpen (U ∪ V)
  := by
  rw [Set.union_eq_iUnion]
  exact (isOpen_iUnion (Bool.forall_bool.2 ⟨V_is_open, U_is_open⟩))

theorem universal_property_quotient_space
  {π : X → Y}
  (π_is_quotient : QuotientMap π)
  (f : Y → Z)
  : Continuous f ↔ Continuous (f ∘ π)
  := by
  have π_is_continuous : Continuous π := π_is_quotient.continuous
  have lemma_if (H : Continuous f) : Continuous (f ∘ π) := by
    exact Continuous.comp H π_is_continuous
  have lemma_only_if (H : Continuous (f ∘ π)) : Continuous f := by
    rw [continuous_iff_coinduced_le]
    rw [π_is_quotient.right]
    rw [coinduced_compose]
    exact continuous_iff_coinduced_le.mp H
  exact Iff.intro lemma_if lemma_only_if
