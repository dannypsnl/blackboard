import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Eigenspace.Basic

variable
  [CommRing R]
  [AddCommGroup V]
  [Module R V]

theorem eigenvector_extend
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
  exact Module.End.hasEigenvector_iff.mpr ⟨ I , cv_nz ⟩

theorem eigen_zero_implies_not_invertable
  (A : Module.End R V)
  (eigen_zero : A.HasEigenvalue 0)
  (iA : Module.End R V)
  (H : ∀ x y : V, A x = y → iA y = x)
  : False := by
  have b := eigen_zero.exists_hasEigenvector
  obtain ⟨v, P⟩ := b
  have w := P.left
  simp at w
  have nz := P.right
  have id_v : iA 0 = v := H v 0 w
  have linear_map_zz : iA 0 = 0 := by
    exact LinearMap.map_zero iA
  rw [linear_map_zz] at id_v
  exact nz (id (Eq.symm id_v))
