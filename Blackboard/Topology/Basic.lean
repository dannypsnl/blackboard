import Mathlib.Topology.Basic

open Topology

variable
  (X : Type u)
  [TopologicalSpace X]
  (U V W : Set X)

def union_of_opens_is_open
  (U_is_open : IsOpen U)
  (V_is_open : IsOpen V)
  : IsOpen (U ∪ V)
  := by
  rw [Set.union_eq_iUnion]
  exact (isOpen_iUnion (Bool.forall_bool.2 ⟨V_is_open, U_is_open⟩))
