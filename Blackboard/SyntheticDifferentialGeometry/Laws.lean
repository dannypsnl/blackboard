import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Blackboard.SyntheticDifferentialGeometry.Axiom

variable [CommRing R]

axiom KLr : ∀ f : R → R, ∀ x : R, ∃! b : R, ∀ d : SquareZero R, f (x + d.val) = f x + d.val * b

noncomputable def diff (f : R → R) (x : R) : R := (KLr f x).choose

instance : Add (R → R) where
  add f g := fun x ↦ f x + g x
instance : Mul (R → R) where
  mul f g := fun x ↦ f x * g x

theorem sum_rule
  [IsLeftCancelMul R]
  (f g : R → R)
  : ∀ x : R, diff (f + g) x = diff f x + diff g x := by
  intros x
  have F := KLr f x
  have G := KLr g x
  have FG := (KLr (f + g) x).choose_spec
  have unique := FG.right
  have H : ∀ d : SquareZero R, f x + d.val * (diff f x) + g x + d.val * (diff g x) = f x + g x + d.val * (diff f x) + d.val * (diff g x) := by
    intros d
    simp
    exact add_right_comm (f x) (d.val * diff f x) (g x)
  have L' : ∀ d : SquareZero R, f x + d.val * (diff f x) + g x + d.val * (diff g x) = f x + g x + d.val * (diff (f + g) x)
    := by
    intro d
    unfold diff
    rw [←F.choose_spec.left d]
    rw [add_assoc]
    rw [←G.choose_spec.left d]
    exact FG.left d
  have C : ∀ d : SquareZero R, f x + g x + (d.val * (diff f x) + d.val * (diff g x)) = f x + g x + d.val * (diff (f + g) x) := by
    intros d
    have := L' d
    rw [add_assoc, add_assoc] at this
    rw [←add_assoc _ (g x)] at this
    rw [add_comm (d.val * diff f x) (g x)] at this
    rw [←add_assoc, ←add_assoc, add_assoc] at this
    exact this
  have D : ∀ d : SquareZero R, diff f x + diff g x = diff (f + g) x := by
    intros d
    have := C d
    have := add_left_cancel this
    rw [← mul_add] at this
    exact mul_left_cancel (a := d.val) this
  exact Eq.symm (D zero)

theorem product_rule
  [IsLeftCancelMul R]
  (f g : R → R)
  : ∀ x : R, diff (f * g) x = (diff f x) * g x + f x * (diff g x) := by
  intros x
  have F := (KLr f x).choose_spec.left
  have G := (KLr g x).choose_spec.left
  have P := KLr (f * g) x
  have : ∀ (d : SquareZero R), f (x + d.val) * g (x + d.val) = f x * g x + d.val * diff (f * g) x := P.choose_spec.left
  have : ∀ (d : SquareZero R), (f x + d.val * diff f x) * (g x + d.val * diff g x) = f x * g x + d.val * diff (f * g) x := by
    intros d
    have := this d
    rw [F d] at this
    rw [G d] at this
    exact this
  have : ∀ (d : SquareZero R),
    f x * g x + (f x * d.val * diff g x + d.val * diff f x * g x + d.val * diff f x * d.val * diff g x)
    = f x * g x + (d.val * diff (f * g) x) := by
    intros d
    have := this d
    rw [add_mul, mul_add, mul_add] at this
    rw [← mul_assoc] at this
    rw [← mul_assoc] at this
    rw [← add_assoc] at this
    rw [add_assoc (a := f x * g x)] at this
    rw [add_assoc (a := f x * g x)] at this
    exact this
  have : ∀ (d : SquareZero R), f x * d.val * diff g x + d.val * diff f x * g x + d.val * diff f x * d.val * diff g x = d.val * diff (f * g) x := by
    intros d
    have := this d
    have := add_left_cancel (a := f x * g x) this
    exact this
  have : ∀ (d : SquareZero R), f x * d.val * diff g x + d.val * diff f x * g x = d.val * diff (f * g) x := by
    intros d
    have := this d
    rw [mul_assoc d.val (diff f x) d.val] at this
    rw [mul_comm (diff f x) d.val] at this
    rw [← mul_assoc] at this
    simp at this
    exact this
  have : ∀ (d : SquareZero R), f x * diff g x + diff f x * g x = diff (f * g) x := by
    intros d
    have := this d
    rw [mul_comm (f x) d.val] at this
    rw [mul_assoc] at this
    rw [mul_assoc] at this
    rw [←mul_add] at this
    have := mul_left_cancel (a := d.val) this
    exact this
  have := this zero
  rw [add_comm] at this
  exact id (Eq.symm this)

theorem chain_rule
  [IsLeftCancelMul R]
  (f g : R → R)
  : ∀ x : R, diff (f ∘ g) x = diff f (g x) * diff g x := by
  intros x
  have G := (KLr g x).choose_spec.left
  have Chain := (KLr (f ∘ g) x).choose_spec.left
  have : ∀ (d : SquareZero R), (f ∘ g) (x + d.val) = (f ∘ g) x + d.val * diff (f ∘ g) x := Chain
  have : ∀ (d : SquareZero R), (f ∘ g) x + d.val * diff (f ∘ g) x = f (g (x + d.val)) := by
    intro d
    exact (this d).symm
  have : ∀ (d : SquareZero R), (f ∘ g) x + d.val * diff (f ∘ g) x = f (g x + d.val * diff g x) := by
    intro d
    have := this d
    rw [G d] at this
    exact this
  have : ∀ (d : SquareZero R), (f ∘ g) x + d.val * diff (f ∘ g) x = f (g x) + d.val * diff g x * diff f (g x) := by
    intro d
    let ready : SquareZero R := {
      val := d.val * diff g x
      property := by
        unfold IsSquareZero
        rw [←mul_assoc]
        rw [mul_comm _ d.val]
        rw [←mul_assoc]
        simp
    }
    have F : f (g x + d.val * diff g x) = f (g x) + d.val * diff g x * diff f (g x) := (KLr f (g x)).choose_spec.left ready
    rw [←F]
    exact this d
  have : ∀ (d : SquareZero R), d.val * diff (f ∘ g) x = d.val * (diff g x * diff f (g x)) := by
    intro d
    have := this d
    rw [mul_assoc] at this
    exact add_left_cancel this
  have : ∀ (d : SquareZero R), diff (f ∘ g) x = diff g x * diff f (g x) := by
    intro d
    have := this d
    exact mul_left_cancel (a := d.val) this
  have := this zero
  rw [mul_comm]
  exact this
