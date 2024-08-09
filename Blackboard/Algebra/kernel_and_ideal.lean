import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.RingHomProperties
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

variable
  {R S : Type u}
  [Ring R] [Ring S]

abbrev Ker (ϕ : RingHom R S) := { r : R // ϕ r = 0 }

theorem kernel_is_ideal
  (ϕ : RingHom R S)
  (a b : Ker ϕ)
  (r : R)
  : ϕ (a - b) = 0 ∧ ϕ (a * r) = 0 ∧ ϕ (r * a) = 0
  := by
  have ϕa_is_unit := a.prop
  have ϕb_is_unit := b.prop
  have lemma₁ : ϕ (a - b) = (ϕ a) - (ϕ b) := by
    exact RingHom.map_sub ϕ ↑a ↑b
  have lemma₂ : (ϕ a) - (ϕ b) = 0 := by
    rw [ϕa_is_unit, ϕb_is_unit]
    exact zero_sub_zero
  have lemma₃ : ϕ (a * r) = (ϕ a) * (ϕ r) := by
    exact RingHom.map_mul ϕ (↑a) r
  have lemma₄ : ϕ (r * a) = (ϕ r) * (ϕ a) := by
    exact RingHom.map_mul ϕ r (↑a)
  have lemma₅ : (ϕ a) * (ϕ r) = 0 := by
    rw [ϕa_is_unit]
    exact zero_mul (ϕ r)
  have lemma₆ : ϕ r * ϕ a = 0 := by
    rw [ϕa_is_unit]
    exact mul_zero (ϕ r)
  rw [lemma₁, lemma₂, lemma₃, lemma₄, lemma₅, lemma₆]
  exact ⟨rfl, rfl, rfl⟩
