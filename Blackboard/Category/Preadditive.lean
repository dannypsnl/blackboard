import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory
open CategoryTheory.Limits

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

theorem always_biproduct
  [Category C]
  [Preadditive C]
  (A B : C)
  [HasBinaryProduct A B]
  : HasBinaryCoproduct A B := by
  have isLimit := limit.isLimit (pair A B)
  have bc := binaryBiconeIsBilimitOfLimitConeOfIsLimit isLimit
  let cc := BinaryBicone.ofLimitCone isLimit
  exact HasColimit.mk { cocone := cc.toCocone, isColimit := bc.isColimit }

/-- `IsEq e f g` is say the morphism `e` is the equalizer of `f` and `g`
  and it's the universal object with this property -/
class IsEq [Category C] {A B L : C} (e : L ⟶ A) (f g : A ⟶ B) : Prop where
  prop : e ≫ f = e ≫ g
  factor : (k : X ⟶ A) → k ≫ f = k ≫ g → ∃! s : X ⟶ L, k = s ≫ e

theorem is_eq_is_mono
  [Category C]
  {A B : C}
  (e : L ⟶ A)
  (f g : A ⟶ B)
  (eq : IsEq e f g)
  : Mono e := {
  right_cancellation a b ea_eq_eb := by
    have : (a ≫ e) ≫ f = (a ≫ e) ≫ g := by
      simp
      rw [eq.prop]
    have A := eq.factor (a ≫ e) this
    have s_uniq := A.choose_spec.2
    have B_eq : b = A.choose := by
      rw [s_uniq b]
      simp
      exact ea_eq_eb
    have A_eq : a = A.choose := s_uniq a rfl
    rw [A_eq]
    rw [B_eq]
}

noncomputable def equalizer_is_unique
  [Category C]
  (A B : C)
  (e1 : L1 ⟶ A)
  (e2 : L2 ⟶ A)
  (f g : A ⟶ B)
  (H1 : IsEq e1 f g)
  (H2 : IsEq e2 f g)
  : L1 ≅ L2 :=
  let h1 : ∃! a, e2 = e1 ⊚ a := H1.factor e2 H2.prop
  let h2 : ∃! b, e1 = e2 ⊚ b := H2.factor e1 H1.prop
  let a := h1.choose
  let b := h2.choose
{
  hom := b
  inv := a
  hom_inv_id := by
    have : e1 = e2 ⊚ b := h2.choose_spec.1
    have : e1 ⊚ 𝟙 _ = e1 ⊚ a ⊚ b := by
      simp
      rw [←h1.choose_spec.1]
      exact this
    have cancel : Mono e1 := is_eq_is_mono e1 f g H1
    rw [cancel_mono e1] at this
    exact id (Eq.symm this)
  inv_hom_id := by
    have : e2 = e1 ⊚ a := h1.choose_spec.1
    have : e2 ⊚ 𝟙 _ = e2 ⊚ b ⊚ a := by
      simp
      rw [←h2.choose_spec.1]
      exact this
    have cancel : Mono e2 := is_eq_is_mono e2 f g H2
    rw [cancel_mono e2] at this
    exact id (Eq.symm this)
}

theorem equalizer_is_commutative
  [Category C]
  (A B : C)
  (e : L ⟶ A)
  (f g : A ⟶ B)
  : IsEq e f g → IsEq e g f := by
  intros H
  exact {
    prop := Eq.symm H.prop
    factor k P := H.factor k (Eq.symm P)
  }

/-- If we further knew C is preadditive, we can have the concept of kernel of `k` which is the equalizer of `h` and `0` -/
abbrev IsKer
  [Category C]
  [Preadditive C]
  {A B L : C} (e : L ⟶ A) (h : A ⟶ B) :=
  IsEq e h 0

theorem kernel_equiv
  [Category C]
  [Preadditive C]
  (A B : C)
  (e : L ⟶ A)
  (f g : A ⟶ B)
  : IsEq e f g ↔ IsKer e (f - g) := Iff.intro IF ONLY_IF
  where
  IF : IsEq e f g → IsKer e (f - g) := by
    intros has_eq_f_g
    exact {
      prop := by
        simp
        have : e ≫ f = e ≫ g := has_eq_f_g.prop
        exact sub_eq_zero_of_eq this
      factor k kf_minus_kg := by
        simp at kf_minus_kg
        have : k ≫ f = k ≫ g := by
          exact eq_of_sub_eq_zero kf_minus_kg
        have : ∃! s , k = s ≫ e := has_eq_f_g.factor k this
        exact this
    }
  ONLY_IF : IsKer e (f - g) → IsEq e f g := by
    intros has_ker
    exact {
      prop := by
        have := has_ker.prop
        simp at this
        exact eq_of_sub_eq_zero this
      factor k kf_eq_kg := by
        have : (f - g) ⊚ k = 0 ⊚ k := by
          simp
          exact sub_eq_zero_of_eq kf_eq_kg
        have : ∃! s , k = s ≫ e := has_ker.factor k this
        exact this
    }
