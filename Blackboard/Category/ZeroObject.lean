import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

variable
  {C : Type u} [CategoryTheory.Category.{v, u} C]

open CategoryTheory
open CategoryTheory.Limits

theorem zero_object_unique_to_any
  {Z : C}
  (self : IsZero Z)
  (X : C)
  : Nonempty (Unique (Z ⟶ X))
  := self.unique_to X
theorem zero_object_unique_from_any
  {Z : C}
  (self : IsZero Z)
  (X : C)
  : Nonempty (Unique (X ⟶ Z))
  := self.unique_from X

-- But how to prove it's unique in this way?
-- The point is, A ⟶ B can have more morphisms, but the A ⟶ 0 ⟶ B only this one
theorem construct_zero_morphism
  {Z : C}
  (self : IsZero Z)
  (A B : C)
  (f : A ⟶ Z := self.from_ A)
  (g : Z ⟶ B := self.to_ B)
  : Nonempty (A ⟶ B)
  := by
  exact .intro (f ≫ g)

theorem mono_after_g_is_0_then_g_is_0 (H : HasZeroMorphisms C) {X Y Z : C}
  (g : X ⟶ Y)
  (f : Y ⟶ Z) [f_is_Mono : Mono f]
  (P : g ≫ f = 0)
  : g = 0
  := by
  rw [←(H.zero_comp X f)] at P
  exact (f_is_Mono.right_cancellation g 0) P
