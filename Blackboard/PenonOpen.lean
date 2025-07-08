def P (X : Type u) := X → Prop

notation x "∈" U => U x

structure Open (U : P X) : Type v where
  prop : ∀ x : X, ∀ y : X, (x ∈ U) → y ≠ x ∨ y ∈ U

def subset (U V : P X) := ∀ x : X, U x → V x
notation U "⊆" V => subset U V

theorem intrinsic_open_property
  (U : P X)
  (O : Open U)
  : ∀ x : X, U x → (fun y : X ↦ ¬¬(y = x)) ⊆ U := by
  intros x x_in_U
  intros y not_not_y_eq_x
  have o := (O.prop x y) x_in_U
  induction o
  case inl y_ne_x =>
    exact False.elim (not_not_y_eq_x y_ne_x)
  case inr P =>
    exact P
