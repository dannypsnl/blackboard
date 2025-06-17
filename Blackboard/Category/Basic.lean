import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.FullyFaithful

variable [CategoryTheory.Category.{v, u} C]

open CategoryTheory
open Category

structure IsInverse {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) where
  left : f ≫ g = 𝟙 X
  right : g ≫ f = 𝟙 Y

theorem inverse_is_unique
  (Y : C)
  (f : X ⟶ Y)
  (g k : Y ⟶ X)
  (Hg : IsInverse f g)
  (Hk : IsInverse f k)
  : g = k := by
  have A := Hg.right =≫ k
  have B := Hk.right =≫ k
  rw [←B] at A
  simp [assoc] at A
  rw [Hk.left] at A
  simp [comp_id] at A
  exact A
