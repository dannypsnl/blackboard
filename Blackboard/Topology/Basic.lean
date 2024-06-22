import Mathlib.Topology.Basic

open Topology

variable
  (X : Type u)
  [TopologicalSpace X]
  (U V W : Set X)

-- NOTE: of course, it's unusal to "prove" this. Since in axiomatized topology, this is an axiom.
def union_of_opens_is_open
  (U_is_open : IsOpen U)
  (V_is_open : IsOpen V)
  : IsOpen (U ∪ V)
  := by
  rw [Set.union_eq_iUnion]
  exact (isOpen_iUnion (Bool.forall_bool.2 ⟨V_is_open, U_is_open⟩))
