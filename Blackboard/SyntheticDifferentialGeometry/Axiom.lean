import Mathlib.Algebra.Ring.Basic

variable [CommRing R]

def IsSquareZero (v : R) : Prop := v * v = 0
@[pp_using_anonymous_constructor]
structure SquareZero (R : Type*) [CommRing R] where
  val : R
  property : IsSquareZero val

def zero : SquareZero R := { val := 0, property := zero_mul 0 }

@[simp]
lemma D_mul (a : R) : zero.val * a = 0 := mul_eq_zero_of_left rfl a
@[simp]
lemma D_square_zero (d : SquareZero R)
  : d.val * d.val = (0 : R) := d.property

axiom KL : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b

def α (pair : R × R) : (SquareZero R → R) :=
  fun d ↦ pair.fst + d.val * pair.snd

axiom KL' : Function.Bijective (α (R := R))

theorem KL_implies_KL'
  (KL : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b)
  : Function.Bijective (α (R := R)) := {
  left := by
    intros p1 p2 f1_eq_f2
    have eq : ∀ d, (α p1) d = (α p2) d := by
      exact fun d ↦ congrFun f1_eq_f2 d
    have definition : (α p1) zero = p1.1 := by
      (expose_names; refine Eq.symm ((fun {α β} {p} ↦ Prod.fst_eq_iff.mpr) ?_))
      simp
    have definition2 : (α p2) zero = p2.1 := by
      (expose_names; refine Eq.symm ((fun {α β} {p} ↦ Prod.fst_eq_iff.mpr) ?_))
      simp
    have eqz := eq zero
    rw [definition, definition2] at eqz

    have KL1 := KL (α p1)
    have KL2 := KL (α p2)
    have joke : ∀ d, α p1 d = α p1 zero + d.val * p1.2 := by
      intros d
      refine eq_add_of_sub_eq' ?_
      rw [definition]
      exact sub_eq_of_eq_add' rfl
    have definition := KL1.unique KL1.choose_spec.1 joke
    rw [←f1_eq_f2] at KL2
    have joke2 : ∀ d, α p1 d = α p1 zero + d.val * p2.2 := by
      intros d
      refine eq_add_of_sub_eq' ?_
      rw [f1_eq_f2]
      rw [definition2]
      exact sub_eq_of_eq_add' rfl
    have definition2 := KL2.unique KL2.choose_spec.1 joke2

    have R : p1.2 = p2.2 := by
      rw [←definition2]
      rw [←definition]

    refine Prod.ext_iff.mpr ?_
    exact ⟨ eqz, R ⟩
  right := by
    intros f
    have ap := KL f
    let a := f zero
    let b := ap.choose
    refine Exists.intro (a, b) ?_
    funext d
    unfold α
    simp [a, b]
    exact (ap.choose_spec.1 d).symm
}
