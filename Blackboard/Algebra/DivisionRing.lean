import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Divisibility.Basic

variable
  {R : Type u}

theorem only_ideals_of_division_ring_are_zero_and_itself
  [DivisionRing R]
  (I : Ideal R)
  : I = Ideal.span { 0 } ∨ I = ⊤ := by
  have P := DivisionRing.isPrincipalIdealRing R
  have I_is_principal := P.principal I
  exact I_is_principal.principal.elim fun x S => by
    rw [S]
    have K := Ideal.mem_span_singleton_self x
    by_cases H : x = 0
    case pos =>
      rw [H]
      exact Or.inl (Submodule.ext (fun x ↦ Eq.to_iff rfl))
    case neg =>
      have x_isUnit : IsUnit x := Ne.isUnit H
      have one := (Ideal.span_singleton_mul_left_unit x_isUnit) 1
      simp at one
      rw [Ideal.submodule_span_eq]
      rw [one]
      exact Or.inr rfl
