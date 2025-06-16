def FixedPointed (A : Type u) : Prop :=
  ∀ f : A → A, ∃ x : A, f x = x

theorem rice
  (HasFixedPoint : FixedPointed A)
  : ∀ f : A → Bool, ∀ x y : A, f x = f y
  := by
  intros f x y
  let g z := if (f z = f y) then x else y
  have g_fix := HasFixedPoint g
  obtain ⟨u, H⟩ := g_fix
  have boolDec : Decidable (f u = f y) := Bool.decEq (f u) (f y)
  induction boolDec
  case isTrue fu_eq_fy =>
    have A : x = g u := (if_pos fu_eq_fy).symm
    rw [A, H]
    exact fu_eq_fy
  case isFalse fu_ne_fy =>
    have A : g u = y := if_neg fu_ne_fy
    rw [H] at A
    have B : f u = f y := congrArg f A
    exact False.elim (fu_ne_fy B)
