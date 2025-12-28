import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations

variable
  [CommRing R]

theorem exercise_0_4
  (I J K : Ideal R)
  : I * (J + K) = I * J + I * K := by
  rw [add_eq_sup, add_eq_sup]
  exact Ideal.mul_sup I J K
