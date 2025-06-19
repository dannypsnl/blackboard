import Mathlib.Algebra.Ring.Basic

variable
  [CommRing R]

@[pp_using_anonymous_constructor]
structure SquareZero (R : Type*) [CommRing R] where
  val : R
  property : val * val = 0
def zero : SquareZero R := { val := 0, property := zero_mul 0 }
theorem sqr_zero_mul (a : R) : zero.val * a = 0 := by
  exact mul_eq_zero_of_left rfl a

axiom KL : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b

def f (b : R) (d : SquareZero R) : R := d.val * b

theorem all_products_are_same_determine_an_unique_element_of_R
  (b1 b2 : R)
  (H : ∀ d : SquareZero R, d.val * b1 = d.val * b2)
  : b1 = b2 := by
  let f1 := f b1
  have b11 (d : SquareZero R) : f1 d = 0 + d.val * b1 := by
    simp [zero_add]
    exact rfl
  have b22 (d : SquareZero R) : f1 d = 0 + d.val * b2 := by
    simp [zero_add]
    exact H d
  have cc := KL f1
  have f1zz : f1 zero = 0 := sqr_zero_mul b1
  rw [f1zz] at cc
  exact ExistsUnique.unique cc b11 b22

lemma square {a b : R} : a = b → a * a = b * b := by
  intros H
  rw [H]

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
  have ne_zero := d₀.property
  have eq_one : g d₀ = 1 := if_neg ne_zero
  rw [eq_one] at h
  have R := square h
  rw [←mul_assoc, mul_comm _ b, mul_comm _ b, mul_assoc] at R
  have sq_zero := d₀.val.property
  rw [sq_zero] at R
  simp at R
