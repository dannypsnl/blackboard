import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

class VectorSpace
  (S : Type u) [One S] [Add S] [Mul S]
  (V : Type u) [Zero V] [Add V] [Neg V]
  : Type u where
  sym : {x y : V} → x + y = y + x
  assoc : {x y z : V}
    → (x + y) + z
      = x + (y + z)
  unity : {x : V} → 0 + x = x

  cancel : {x : V} → (- x) + x = 0

  mul : S → V → V
  distribute_scalar : {s1 s2 : S} → {v : V} → mul (s1 + s2) v = mul s1 v + mul s2 v
  distribute_vector : {c : S} → {x y : V} → mul c (x + y) = mul c x + mul c y
  scalar_prod : {c d : S} → {v : V} → mul (d * c) v = mul c (mul d v)
  scalar_unity : {v : V} → mul 1 v = v

def VReal := { r : Real // 0 < r } deriving
  One, CommMonoid
notation "ℝ>0" => VReal
instance : Zero ℝ>0 where
  zero := 1
instance : Add ℝ>0 where
  add x y := ⟨ x.val * y.val , by refine mul_pos x.property y.property ⟩
noncomputable instance : Div ℝ>0 where
  div x y := ⟨ x.val / y.val , by refine div_pos x.property y.property ⟩
noncomputable instance : Neg ℝ>0 where
  neg x := 1 / x
noncomputable instance : HPow ℝ>0 ℝ ℝ>0 where
  hPow x y :=
    ⟨ Real.rpow x.val y , Real.rpow_pos_of_pos x.property y ⟩

theorem outside_cancel {x : ℝ>0} : (1 / x.val) * x.val = 1 := by
  have x_ne_zero : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)
  exact one_div_mul_cancel x_ne_zero

noncomputable instance : VectorSpace ℝ ℝ>0 where
  sym {x y} := CommMonoid.mul_comm x y
  assoc {x y z} := mul_assoc x y z
  unity {x} := one_mul x
  cancel {x} := by
    have x_ne_zero : x.val ≠ 0 := Ne.symm (ne_of_lt x.property)
    have H := one_div_mul_cancel x_ne_zero
    rw [← Subtype.val_inj]
    norm_cast
  mul c x := x ^ c
  distribute_scalar {s1 s2} {v} := by
    have K := Real.rpow_add v.property s1 s2
    rw [← Subtype.val_inj]
    norm_cast
  distribute_vector {c} {x y} := by
    have K :=
      Real.mul_rpow (le_of_lt x.property) (le_of_lt y.property) (z := c)
    rw [← Subtype.val_inj]
    norm_cast
  scalar_prod {c d} {v} := by
    have K := Real.rpow_mul (le_of_lt v.property) d c
    simp
    rw [← Subtype.val_inj]
    norm_cast
  scalar_unity {v} := by
    have K := Real.rpow_one v.val
    rw [← Subtype.val_inj]
    norm_cast
