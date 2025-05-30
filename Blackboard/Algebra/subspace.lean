import Mathlib.Data.Set.Defs
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.LinearMap.End

variable
  [CommRing R]
  [AddCommGroup V]
  [Module R V]

theorem ker_endo_is_subspace
  (A : Module.End R V)
  (Ker := { x | A x = 0 })
  : ∀ l : R, ∀ v w : Ker, A (v + l • w) = 0 := by
  intros l v w
  have c : ∀ a : Ker, A a = 0 := by
    apply?
  have b : A v = 0 := c v
  rw [←b]
