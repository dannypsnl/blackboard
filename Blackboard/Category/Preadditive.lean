import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory
open CategoryTheory.Limits

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

variable
  {C : Type u}
  [Category.{v, u} C]
  [Preadditive C]
  [HasZeroObject C]

theorem always_biproduct
  (A B : C)
  [HasBinaryProduct A B]
  : HasBinaryCoproduct A B := by
  let P := prod A B
  let coneA : Cone (pair A B) := { pt := A, π := mapPair (𝟙 A) 0 }
  let coneB : Cone (pair A B) := { pt := B, π := mapPair 0 (𝟙 B) }
  let sA : A ⟶ P := by
    exact prod.inl coneA.pt B
  let sB : B ⟶ P := by
    exact prod.inr A coneB.pt
  let PAsCocone : Cocone (pair A B) := { pt := P, ι := mapPair sA sB }
  have PIsColimit : IsColimit PAsCocone := by
    sorry
  let Q : ColimitCocone (pair A B) := { cocone := PAsCocone, isColimit := PIsColimit }
  have P : Nonempty (ColimitCocone (pair A B)) := Nonempty.intro Q
  exact { exists_colimit := P  }
