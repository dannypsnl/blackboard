import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.RingHomProperties
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

variable [Ring R] [Ring S]

abbrev Ker (ϕ : R →+* S) := { r : R // ϕ r = 0 }

theorem kernel_is_ideal
  (ϕ : R →+* S)
  (a b : Ker ϕ)
  (r : R)
  : ϕ (a - b) = 0 ∧ ϕ (a * r) = 0 ∧ ϕ (r * a) = 0
  := by
  have ϕa_is_unit := a.prop
  have ϕb_is_unit := b.prop
  rw [ϕ.map_sub ↑a ↑b]
  rw [ϕ.map_mul (↑a) r, ϕ.map_mul r (↑a)]
  rw [ϕa_is_unit, ϕb_is_unit]
  rw [zero_sub_zero, zero_mul (ϕ r), mul_zero (ϕ r)]
  exact ⟨rfl, rfl, rfl⟩

open Ideal.Quotient

theorem ideal_is_kernel
  {R : Type u}
  [CommRing R]
  (I : Ideal R)
  : ∀ x : R, (mk I) x = 0 ↔ ↑x ∈ I
  := by
  intros x
  exact eq_zero_iff_mem (R := R)
