import Mathlib.Algebra.Ring.Defs

-- This file is trying to model the idea of the field of fractions
-- Let R be an ideal domain
-- then R × R\{0} with quotient that
--   a/s = b/t
-- if and only if
--   at = sb
-- hence we define the _H argument (didn't required in proof, but important in concept)
variable
  [CommRing R]

def equiv (a b : R × R) : Prop := a.1 * b.2 = a.2 * b.1
notation:20 a " ≈ " b => equiv a b

-- Any denominator is fine
-- notice that a ≠ 0
lemma denominator_didn't_matter
  : ∀ a : R, (0, a) ≈ (0, 1) := by
  intro a
  have : 0 * 1 = a * 0 := by
    simp
  exact this

-- a/s = 0/1 if and only if a = 0
theorem equiv_to_zero_means_numerator_is_zero
  (a : R × R)
  (_H : ∀ a : R × R, a.2 ≠ 0)
  : (a ≈ (0, 1)) ↔ a.1 = 0 := by
  constructor
  intro P
  have : a.1 * 1 = a.2 * 0 := P
  simp at this
  exact this
  intro a_is_0
  have : a.1 * 1 = a.2 * 0 := by
    rw [a_is_0]
    simp
  exact this

def IsTorsion (a : R × R) : Prop :=
  ∃ r ≠ 0, (r * a.1 , a.2) ≈ (0, 1)

-- If a is a torsion, then a = 0/1
theorem torsion_free
  [NoZeroDivisors R]
  (_H : ∀ a : R × R, a.2 ≠ 0)
  : ∀ a : R × R, IsTorsion a → (a ≈ (0, 1)) := by
  intro a is_torsion
  have is_torsion : ∃ r ≠ 0, (r * a.1 , a.2) ≈ (0, 1) := is_torsion
  let r := is_torsion.choose
  have r_ne_0 := is_torsion.choose_spec.left
  have rH := is_torsion.choose_spec.right
  have : r * a.1 * 1 = a.2 * 0 := rH
  simp at this
  rcases this with (r_is_0 | a_is_0)
  case inl =>
    exact False.elim (r_ne_0 r_is_0)
  case inr =>
    have : a.1 * 1 = a.2 * 0 := by
      rw [a_is_0]
      simp
    exact this
