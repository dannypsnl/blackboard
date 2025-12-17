import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory
open CategoryTheory.Limits

class IsCoeq [Category K] {A B L : K} (e : B ⟶ L) (f g : A ⟶ B) : Prop where
  prop : f ≫ e = g ≫ e
  factor : (k : B ⟶ X) → f ≫ k = g ≫ k → ∃! s , k = e ≫ s
abbrev IsCoker [Category K] [Preadditive K] {A B L : K}
  (c : B ⟶ L) (h : A ⟶ B) :=
  IsCoeq c h 0

noncomputable section

variable
  [Category K]
  [Preadditive K]
  [HasBinaryBiproducts K]

abbrev p1 {X Y : K} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X := biprod.fst
abbrev p2 {X Y : K} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y := biprod.snd
abbrev s1 {X Y : K} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y := biprod.inl
abbrev s2 {X Y : K} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y := biprod.inr

theorem diagonal_is_characterized_by_projections_sub
  (C : K)
  (ΔC : C ⟶ C ⊞ C)
  (H1 : 𝟙 C = ΔC ≫ p1)
  (H2 : 𝟙 C = ΔC ≫ p2)
  : IsCoker (p1 - p2) ΔC := by
  have FST : (s1 + s2) ≫ p1 = ΔC ≫ p1 := by calc
    (s1 + s2) ≫ p1 = s1 ≫ p1 + s2 ≫ p1 := by
      exact Preadditive.add_comp C (C ⊞ C) C s1 s2 p1
    _ = 𝟙 C := by
      rw [biprod.inr_fst]
      simp
    _ = ΔC ≫ p1 := by
      exact H1
  have SND : (s1 + s2) ≫ p2 = ΔC ≫ p2 := by calc
    (s1 + s2) ≫ p2 = s1 ≫ p2 + s2 ≫ p2 := by
      exact Preadditive.add_comp C (C ⊞ C) C s1 s2 p2
    _ = 𝟙 C := by
      rw [biprod.inl_snd]
      simp
    _ = ΔC ≫ p2 := by
      exact H2
  have CHAR : s1 + s2 = ΔC := by
    refine biprod.hom_ext (biprod.inl + biprod.inr) ΔC FST ?_
    exact SND

  exact {
    prop := by calc
      ΔC ≫ (p1 - p2 : C ⊞ C ⟶ C) = (s1 + s2) ≫ (p1 - p2) := by
        exact congrFun (congrArg CategoryStruct.comp (id (Eq.symm CHAR))) (p1 - p2)
      _ = (s1 + s2) ≫ p1 - (s1 + s2) ≫ p2 := by
        exact Preadditive.comp_sub (s1 + s2) p1 p2
      _ = (s1 ≫ p1 + s2 ≫ p1) - (s1 ≫ p2 + s2 ≫ p2) := by
        rw [Preadditive.add_comp _ _ _ s1 s2 p1]
        rw [Preadditive.add_comp _ _ _ s1 s2 p2]
      _ = ((s1 : C ⟶ C ⊞ C) ≫ p1) - ((s2 : C ⟶ C ⊞ C) ≫ p2) := by
        rw [biprod.inl_snd]
        rw [biprod.inr_fst]
        simp
      _ = 𝟙 C - (s2 ≫ p2) := by
        rw [biprod.inl_fst]
      _ = 𝟙 C - 𝟙 C := by rw [biprod.inr_snd]
      _ = 0 := by exact sub_self (𝟙 C)
      _ = 0 ≫ (p1 - p2) := by
        rw [zero_comp]
    factor {D} f H := by
      refine Exists.intro (s1 ≫ f) ?_
      have KK : s1 ≫ f + s2 ≫ f = 0 := by
        rw [←Preadditive.add_comp _ _ _ s1 s2 f]
        rw [CHAR, H]
        rw [zero_comp]
      have KEY : s1 ≫ f = - s2 ≫ f := by
        exact eq_neg_of_add_eq_zero_left KK

      exact {
        left := Eq.symm (calc
          (p1 - p2) ≫ (s1 ≫ f) = ((p1 - p2) ≫ s1) ≫ f := by
            rw [Category.assoc]
          _ = (p1 ≫ s1 - p2 ≫ s1) ≫ f := by
            rw [Preadditive.sub_comp p1 p2 s1]
          _ = (p1 ≫ s1) ≫ f - (p2 ≫ s1) ≫ f := by
            exact Preadditive.sub_comp (p1 ≫ s1) (p2 ≫ s1) f
          _ = (p1 ≫ s1) ≫ f - p2 ≫ (s1 ≫ f) := by
            rw [←Category.assoc]
          _ = (p1 ≫ s1) ≫ f + p2 ≫ (s2 ≫ f) := by
            rw [KEY]
            simp
          _ = (p1 ≫ s1) ≫ f + (p2 ≫ s2) ≫ f := by
            simp
          _ = (p1 ≫ s1 + p2 ≫ s2) ≫ f := by
            exact Eq.symm (Preadditive.add_comp (C ⊞ C) (C ⊞ C) D (p1 ≫ s1) (p2 ≫ s2) f)
          _ = 𝟙 (C ⊞ C) ≫ f := by
            rw [biprod.total]
          _ = f := Category.id_comp f
        )
        right g0 P := Eq.symm (calc
          s1 ≫ f = s1 ≫ (p1 - p2) ≫ g0 := by
            rw [P]
          _ = (s1 ≫ (p1 - p2)) ≫ g0 := by
            rw [Category.assoc]
          _ = ((s1 : C ⟶ C ⊞ C) ≫ p1 - s1 ≫ p2) ≫ g0 := by
            rw [Preadditive.comp_sub s1 p1 p2]
          _ = (𝟙 C - 0) ≫ g0 := by
            rw [biprod.inl_fst]
            rw [biprod.inl_snd]
          _ = g0 := by
            simp
        )
      }
  }

-- And a + b = a - (0 - b) hence this is enought to recover
theorem morphism_add_is_characterized_by_biproduct
  (C : K)
  (a b : A ⟶ C)
  : ∃ c : A ⟶ C ⊞ C, a - b = c ≫ (p1 - p2) := by
  let c := Limits.biprod.lift a b
  exists c
  calc
    a - b = c ≫ p1 - c ≫ p2 := by
      rw [biprod.lift_fst a b]
      rw [biprod.lift_snd a b]
    _ = c ≫ (p1 - p2) := by
      rw [Preadditive.comp_sub c p1 p2]
