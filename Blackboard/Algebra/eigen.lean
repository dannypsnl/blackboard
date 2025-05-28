import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Eigenspace.Basic

theorem eigenvector_extend
  [CommRing R]
  [AddCommGroup V]
  [Module R V]
  [NoZeroSMulDivisors R V]
  (A : Module.End R V)
  (l : R)
  (v : V)
  (eigen : A.HasEigenvector l v)
  (c : R) (c_nz : c ≠ 0)
  : A.HasEigenvector l (c • v) := by
  have cv_nz : c • v ≠ 0 := by
    refine smul_ne_zero_iff.mpr ?_
    exact ⟨ c_nz , eigen.right ⟩
  have I : c • v ∈ A.eigenspace l := by
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have coeffient_out := A.map_smul c v
    have ee := eigen.apply_eq_smul
    rw [ee] at coeffient_out
    rw [smul_comm]
    exact coeffient_out
  refine Module.End.hasEigenvector_iff.mpr ?_
  exact ⟨ I , cv_nz ⟩
