import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Blackboard.SyntheticDifferentialGeometry.Axiom

variable
  [CommRing R]

theorem all_products_are_same_determine_an_unique_element_of_R
  (b1 b2 : R)
  (H : ∀ d : SquareZero R, d.val * b1 = d.val * b2)
  : b1 = b2 := by
  let f (b : R) (d : SquareZero R) : R := d.val * b
  let f1 := f b1
  have b11 (d : SquareZero R) : f1 d = 0 + d.val * b1 := by
    simp [zero_add]
    exact rfl
  have b22 (d : SquareZero R) : f1 d = 0 + d.val * b2 := by
    simp [zero_add]
    exact H d
  have cc := KL f1
  have f1zz : f1 zero = 0 := D_mul b1
  rw [f1zz] at cc
  exact ExistsUnique.unique cc b11 b22

lemma mul_cong (a b c : R) : b = c → a * b = a * c := by
  exact fun a_1 ↦ congrArg (fun x ↦ a * x) a_1

theorem Schanuel_SDG_incompatible_with_Classical
  [Nontrivial R]
  (h : Nonempty { d : SquareZero R // d.val ≠ 0 })
  [c : ∀ d : SquareZero R, Decidable (d.val = 0)]
  : False := by
  let d₀ := Classical.choice h
  let g (d : SquareZero R) : R := if d.val = 0 then 0 else 1
  obtain ⟨b, P⟩ := KL g
  have h : g d₀ = d₀.val.val * b := by
    have eq_zero : g zero = 0 := if_pos rfl
    rw [P.left]
    simp [eq_zero]
  have eq_one : g d₀ = 1 := if_neg d₀.property
  rw [eq_one] at h
  have square {a b : R} (H : a = b) : a * a = b * b := by rw [H]
  have C := mul_cong d₀.val.val 1 (d₀.val.val * b) h
  simp [←mul_assoc] at C
  have d₀_ne_z := d₀.prop
  exact d₀_ne_z C

lemma distribute_add_mul (d1 d2 : SquareZero R)
  : (d1.val + d2.val) * (d1.val + d2.val) = d1.val * d1.val + 2 * (d1.val * d2.val) + d2.val * d2.val := by
  rw [add_mul, mul_add, mul_add]
  rw [d1.property, d2.property]
  simp
  rw [mul_comm]
  exact Eq.symm (two_mul (d2.val * d1.val))
theorem sum_is_square_zero_iff_mul_zero
  (d1 d2 : SquareZero R)
  (I : Invertible (2 : R))
  : IsSquareZero (d1.val + d2.val) ↔ d1.val * d2.val = (0 : R) :=
  Iff.intro
    (by
      intros H
      unfold IsSquareZero at H
      rw [distribute_add_mul] at H
      rw [d1.property, d2.property] at H
      simp at H
      -- Here we implicitly use `Invertible (2 : R)`
      rw [mul_left_eq_iff_eq_invOf_mul] at H
      simp at H
      exact H)
    (by
      intros H
      unfold IsSquareZero
      rw [distribute_add_mul]
      rw [d1.property, d2.property]
      simp
      rw [mul_left_eq_iff_eq_invOf_mul]
      simp
      exact H)
