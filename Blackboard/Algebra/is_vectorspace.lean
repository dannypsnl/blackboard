import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs

class VectorSpace (S : Type u) (V : Type u) : Type u where
  zero_vector : V
  vector_plus : V → V → V

  sym : {x y : V} → vector_plus x y = vector_plus y x
  assoc : {x y z : V}
    → vector_plus (vector_plus x y) z
      = vector_plus x (vector_plus y z)
  unity : {x : V} → vector_plus zero_vector x = x

  inv : V → V
  -- This will need a tons of coe to enable it.
  -- cancel : {x : V} → vector_plus (inv x) x = zero_vector

  -- Use ℝ as scalar is very hard, HPow didn't get defined.

notation x " ⊕ " y => VectorSpace.vector_plus x y
notation x " ⊙ " y => VectorSpace.mul_scalar x y

def VReal := { r : Real // 0 < r } deriving
  One, CommMonoid
notation "ℝ>0" => VReal
instance : Add ℝ>0 where
  add x y := ⟨ x.val + y.val , by refine add_pos x.property y.property ⟩
instance : Mul ℝ>0 where
  mul x y := ⟨ x.val * y.val , by refine mul_pos x.property y.property ⟩
noncomputable instance : HDiv ℝ>0 ℝ>0 ℝ>0 where
  hDiv x y := ⟨ x.val / y.val , by refine div_pos x.property y.property ⟩

theorem outside_cancel {x : ℝ>0} : (1 / x.val) * x.val = 1 := by
  have h : x.val ≠ 0 := by
    refine Ne.symm (ne_of_lt x.property)
  exact one_div_mul_cancel h

noncomputable instance : VectorSpace ℝ ℝ>0 where
  zero_vector := 1
  vector_plus x y := x * y
  inv x := 1 / x
  sym {x y} := CommMonoid.mul_comm x y
  assoc {x y z} := mul_assoc x y z
  unity {x} := one_mul x
