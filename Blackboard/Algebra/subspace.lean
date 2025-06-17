import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.LinearMap.End

variable
  [CommRing R]
  [AddCommGroup V]
  [Module R V]

notation x "∈Ker[" A "]" => A x = 0

theorem ker_endo_is_subspace
  (A : Module.End R V)
  (l : R)
  (P : v ∈Ker[A])
  (Q : w ∈Ker[A])
  : (v + l • w) ∈Ker[A] := by
  have lem := LinearMap.map_add A v (l • w)
  simp [lem, P, Q]
