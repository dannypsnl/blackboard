import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real

class VectorSpace
  (S : Type u) [Add S]
  (V : Type u) [One V] [Add V]
  : Type u where
  sym : {x y : V} → x + y = y + x
  assoc : {x y z : V}
    → (x + y) + z
      = x + (y + z)
  unity : {x : V} → 1 + x = x

  inv : V → V
  cancel : {x : V} → (inv x) + x = 1

  scalar_mul : S → V → V
  ax1 : {s1 s2 : S} → {v : V} → scalar_mul (s1 + s2) v = scalar_mul s1 v + scalar_mul s2 v

def VReal := { r : Real // 0 < r } deriving
  One, CommMonoid
notation "ℝ>0" => VReal
instance : Coe ℝ>0 ℝ where
  coe r := r.val
instance : Add ℝ>0 where
  add x y := ⟨ x.val * y.val , by refine mul_pos x.property y.property ⟩
noncomputable instance : Div ℝ>0 where
  div x y := ⟨ x.val / y.val , by refine div_pos x.property y.property ⟩
noncomputable instance : HPow ℝ>0 ℝ ℝ>0 where
  hPow x y :=
    ⟨ Real.rpow x.val y , Real.rpow_pos_of_pos x.property y ⟩

theorem outside_cancel {x : ℝ>0} : (1 / x.val) * x.val = 1 := by
  have x_ne_zero : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)
  exact one_div_mul_cancel x_ne_zero

noncomputable instance : VectorSpace ℝ ℝ>0 where
  inv x := 1 / x
  sym {x y} := CommMonoid.mul_comm x y
  assoc {x y z} := mul_assoc x y z
  unity {x} := one_mul x
  cancel {x} := by
    have x_ne_zero : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)
    have H := one_div_mul_cancel x_ne_zero
    reduce; congr
  scalar_mul c x := x ^ c
  ax1 {s1 s2} {v} := by
    have K := Real.rpow_add v.property s1 s2
    reduce; congr
