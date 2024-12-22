import Mathlib.Analysis.SpecialFunctions.Pow.Real

def VReal := { r : Real // 0 < r } deriving
  One, CommMonoid
notation "ℝ>0" => VReal
noncomputable instance : HPow ℝ>0 ℝ ℝ>0 where
  hPow x y :=
    ⟨ Real.rpow x.val y , Real.rpow_pos_of_pos x.property y ⟩

noncomputable instance : AddCommMonoid ℝ>0 where
  zero := 1
  add x y := ⟨ x.val * y.val , by refine mul_pos x.property y.property ⟩
  nsmul c x := x ^ c

  add_assoc x y z := mul_assoc x y z
  add_comm x y := mul_comm x y
  add_zero x := mul_one x
  zero_add x := one_mul x

noncomputable instance : Module ℝ ℝ>0 where
  smul c x := x ^ c
  one_smul v := by
    have K := Real.rpow_one v.val
    rw [← Subtype.val_inj]
    norm_cast
  mul_smul r s v:= by
    have K := Real.rpow_mul (le_of_lt v.property) s r
    rw [mul_comm] at K
    rw [← Subtype.val_inj]
    norm_cast
  smul_add r v w := by
    have K :=
      Real.mul_rpow (le_of_lt v.property) (le_of_lt w.property) (z := r)
    rw [← Subtype.val_inj]
    norm_cast
  add_smul r s v := by
    have K := Real.rpow_add v.property r s
    rw [← Subtype.val_inj]
    norm_cast
  smul_zero a := by
    have K := Real.one_rpow a
    rw [← Subtype.val_inj]
    norm_cast
  zero_smul v := by
    have K := Real.rpow_zero v.val
    rw [← Subtype.val_inj]
    norm_cast
