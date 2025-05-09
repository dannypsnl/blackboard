import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Divisibility.Basic

variable
  {R : Type u}

theorem idempotent_is_identity_in_the_ideal_generated_by_it
  [CommRing R]
  (a : R)
  (H : IsIdempotentElem a)
  : ∀ i ∈ Ideal.span { a }, a * i = i := by
  intros i hi
  have i_is_elem := Ideal.mem_span_singleton (x := i) (y := a)
  have a_dvd_i := i_is_elem.mp hi
  have ex_C := exists_eq_mul_right_of_dvd a_dvd_i
  exact ex_C.elim fun c => by
    intro h
    rw [h, ←mul_assoc, H]
