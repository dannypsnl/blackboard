import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory
open CategoryTheory.Limits

local notation:80 g " ⊚ " f:80 => CategoryStruct.comp f g

variable
  [Category.{v, u} C]
  [Preadditive C]

theorem always_biproduct
  (A B : C)
  [HasBinaryProduct A B]
  : HasBinaryCoproduct A B := by
  have isLimit := limit.isLimit (pair A B)
  have bc := binaryBiconeIsBilimitOfLimitConeOfIsLimit isLimit
  let cc := BinaryBicone.ofLimitCone isLimit
  exact HasColimit.mk { cocone := cc.toCocone, isColimit := bc.isColimit }
