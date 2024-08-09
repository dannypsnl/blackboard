import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.RingHomProperties
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic

variable
  {R S : Type u}
  [Ring R] [Ring S]

theorem kernel_is_ideal
  (ϕ : RingHom R S)
  (a b : { r : R // ϕ r = 0 })
  : ϕ (a - b) = 0
  := by
  have ϕa_is_unit := a.prop
  have ϕb_is_unit := b.prop
  have lemma₁ : ϕ (a - b) = (ϕ a) - (ϕ b) := by
    exact RingHom.map_sub ϕ ↑a ↑b
  have lemma₂ : (ϕ a) - (ϕ b) = 0 := by
    rw [ϕa_is_unit, ϕb_is_unit]
    exact zero_sub_zero
  rw [lemma₁, lemma₂]
