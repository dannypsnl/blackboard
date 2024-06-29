import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.FullyFaithful

variable
  {C : Type u₁} [CategoryTheory.SmallCategory C]
  {D : Type u₂} [CategoryTheory.SmallCategory D]
  (X Y Z : C)

open CategoryTheory
