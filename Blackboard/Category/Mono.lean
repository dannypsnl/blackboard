import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful

variable
  [CategoryTheory.Category.{v, u} C]
  [CategoryTheory.Category.{v, u} D]

open CategoryTheory
open Category

theorem faithful_functor_reflects_mono
  (F : C ⥤ D)
  (faithful : ∀ {X Y : C}, ∀ f g : X ⟶ Y, F.map f = F.map g → f = g)
  (f : X ⟶ Y)
  [M : Mono (F.map f)]
  : Mono f := {
  right_cancellation := by
    intros Z g h E
    have : F.map (g ≫ f) = F.map (h ≫ f) := by
      exact congrArg F.map (faithful (g ≫ f) (h ≫ f) (congrArg F.map E))
    rw [F.map_comp] at this
    rw [F.map_comp] at this
    have := M.right_cancellation _ _ this
    exact faithful g h this
}
