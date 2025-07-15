import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Blackboard.SyntheticDifferentialGeometry.Axiom

variable [CommRing R]

axiom KLr : ∀ f : R → R, ∃! b : R, ∀ x : R, ∀ d : SquareZero R, f (x + d.val) = f x + d.val * b

noncomputable def diff (f : R → R) : R := (KLr f).choose

instance : Add (R → R) where
  add f g := fun x ↦ f x + g x

theorem sum_rule
  [IsLeftCancelMul R]
  (f g : R → R)
  : diff (f + g) = diff f + diff g := by
  have F := KLr f
  have G := KLr g
  have FG := KLr (f + g)
  have FG' := FG.choose_spec
  have L := FG'.left
  have unique := FG'.right
  simp at L
  have H : ∀ x : R, ∀ d : SquareZero R, f x + d.val * (diff f) + g x + d.val * (diff g) = f x + g x + d.val * (diff f) + d.val * (diff g) := by
    intros x d
    simp
    exact add_right_comm (f x) (d.val * diff f) (g x)
  have L' : ∀ x : R, ∀ d : SquareZero R, f x + d.val * (diff f) + g x + d.val * (diff g) = f x + g x + d.val * (diff (f + g))
    := by
    intro x d
    unfold diff
    rw [←F.choose_spec.left x d]
    rw [add_assoc]
    rw [←G.choose_spec.left x d]
    exact L x d
  have C : ∀ x : R, ∀ d : SquareZero R, f x + g x + (d.val * (diff f) + d.val * (diff g)) = f x + g x + d.val * (diff (f + g)) := by
    intros x d
    have := L' x d
    rw [add_assoc, add_assoc] at this
    rw [←add_assoc _ (g x)] at this
    rw [add_comm (d.val * diff f) (g x)] at this
    rw [←add_assoc] at this
    rw [←add_assoc] at this
    rw [add_assoc] at this
    exact this
  have D : ∀ d : SquareZero R, diff f + diff g = diff (f + g) := by
    intros d
    have := C 0 d
    have := add_left_cancel (a := f 0 + g 0) this
    rw [← mul_add] at this
    exact mul_left_cancel (a := d.val) this
  have := D zero
  exact id (Eq.symm this)
