import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

variable
  {K : Type u}
  {V : Type v}
  {W : Type l}

def 𝕀 (B : V × W → K) : V → (W -> K) :=
  fun v w => B (v, w)
def down (L : V → (W → K)) : V × W → K :=
  fun (v, w) => (L v) w

theorem adjunction_map_is_the_generator_map_itself (L : V → (W → K)) : 𝕀 (down L) = L := by
  exact rfl

theorem order_n_is_odd_then_skew_symmetric_matrix_has_det_zero
  [Field K] [CharZero K]
  {n : ℕ} (n_isOdd : Odd n)
  (A : Matrix (Fin n) (Fin n) K)
  (skew_sym : -A = A.transpose)
  : A.det = 0 := by
  have F := A.det_neg
  have R : (-A).det = A.transpose.det := congrArg Matrix.det skew_sym
  have S := A.det_transpose
  simp at F
  rw [Odd.neg_one_pow n_isOdd] at F
  rw [R, S] at F
  refine CharZero.eq_neg_self_iff.mp ?_
  simp at F
  exact F
