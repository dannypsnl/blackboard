import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Groupoid

open CategoryTheory
open Functor

-- Groupoid with one object is a group,
-- in this sense a natural transformation of 𝟭 -> 𝟭 is in the center of the group
theorem one_object_groupoid
  [Groupoid Unit]
  (idG : Unit ⥤ Unit := 𝟭 Unit)
  (α : NatTrans idG idG)
  :  ∀ ⦃X : Unit⦄ (f : X ⟶ X), idG.map f ≫ α.app X = α.app x ≫ idG.map f
  := fun ⦃_⦄ f ↦ α.naturality f
