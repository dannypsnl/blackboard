import Mathlib.Algebra.Ring.Basic

variable [CommRing R]

def IsSquareZero (v : R) : Prop := v * v = 0
@[pp_using_anonymous_constructor]
structure SquareZero (R : Type*) [CommRing R] where
  val : R
  property : IsSquareZero val

def zero : SquareZero R := { val := 0, property := zero_mul 0 }

@[simp]
lemma D_mul (a : R) : zero.val * a = 0 := mul_eq_zero_of_left rfl a
@[simp]
lemma D_square_zero (d : SquareZero R)
  : d.val * d.val = (0 : R) := d.property

axiom KL : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b
