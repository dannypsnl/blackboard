import Mathlib.Logic.Relation

theorem quasi_refl
  (R : α → α → Prop)
  (S : Symmetric R)
  (T : Transitive R)
  (I : R a b)
  : R a a ∧ R b b
  := by
  have A : R a a := by
    exact (T I (S I))
  have B : R b b := by
    exact (T (S I) I)
  exact ⟨A, B⟩
