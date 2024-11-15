import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

variable
  {C : Type u} [CategoryTheory.Category.{v, u} C]

open CategoryTheory

theorem zero_object_unique_to_any
  {Z : C}
  (self : CategoryTheory.Limits.IsZero Z)
  (X : C)
  : Nonempty (Unique (Z ⟶ X))
  := self.unique_to X
theorem zero_object_unique_from_any
  {Z : C}
  (self : CategoryTheory.Limits.IsZero Z)
  (X : C)
  : Nonempty (Unique (X ⟶ Z))
  := self.unique_from X
