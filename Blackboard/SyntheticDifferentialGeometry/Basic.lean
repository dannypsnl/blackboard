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
  have b11 : ∀ d : SquareZero R, f1 d = 0 + d.val * b1 := by
    intro d
    exact (AddZeroClass.zero_add (d.val * b1)).symm
  have b22 : ∀ d : SquareZero R, f1 d = 0 + d.val * b2 := by
    intro d
    rw [b11]
    simp [zero_add]
    exact H d
  have cc := KL f1
  have f1zz : f1 zero = 0 := sqr_zero_mul b1
  rw [f1zz] at cc
  exact ExistsUnique.unique cc b11 b22
