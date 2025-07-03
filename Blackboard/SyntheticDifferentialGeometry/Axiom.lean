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

-- Let a := f(0) and b := choose from (KL f)
-- if α is not injective, then exists b₂ satisfies KL, but that's absurd since b is uniquq
-- if α is not surjective, then some f do not follow KL, that's absurd
theorem KL_implies_KL'
  (KL : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b)
  : Function.Bijective (α (R := R)) := {
  -- This is saying that if α(a, b) = α(a', b')
  -- then a = a' and b = b'
  -- So, the point is, let f := α(a, b)
  -- there is a unique k such that f(d) = f(0) + d * k
  --
  -- and since α(a, b) := d ↦ a + d * b, we know that
  -- a + d * b = α(a, b)(d) = α(a, b)(0) + d * k
  -- and hence α(a, b)(0) = a
  -- and b = k
  --
  -- Use the same argument on α(a', b'), we can see k₂ = b', and α(a', b')(0) = a'
  --
  -- We already know α(a, b) = α(a', b'), therefore,
  -- 1. a = α(a, b)(0) = α(a', b')(0) = a'
  -- 2. a + d * k = α(a, b)(d) = α(a', b')(d) = a' + d * k₂
  -- Now we cancel a, a', then k = k₂, hence b = b'
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
  -- For each function f : D → R, we are looking for a pair (a, b) such that
  -- α(a, b) = f
  --
  -- and this is easy
  -- 1. a := f(0)
  -- 2. Pick b from KL axiom
  -- Then by definition, α(a, b) = f
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

-- Let KL' holds, then we define f(0) := π₁ (α⁻¹ f) and b := π₂ (α⁻¹ f)
-- By definition f(d) = f(0) + d * b
-- Consider if b is not unique, but then there exists two pair (a,b) and (a',b') such that image is f, absurd (α is bijective)
theorem KL'_implies_KL
  (KL' : Function.Bijective (α (R := R)))
  : ∀ f : SquareZero R → R, ∃! b : R, ∀ d : SquareZero R, f d = f zero + d.val * b := by
  intros f
  have surj := KL'.right f
  obtain ⟨⟨a, b⟩, hab⟩ := surj
  use b
  constructor
  case h.left =>
    intros d
    rw [←hab]
    unfold α
    simp
  case h.right =>
    intros b' hb'
    have : α (f zero, b') = f := by
      funext d
      exact (hb' d).symm
    have : (f zero, b') = (a, b) := by
      apply KL'.left
      rw [this]
      rw [hab]
    exact (Prod.mk.inj this).2
