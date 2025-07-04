import Mathlib.CategoryTheory.Types

-- Counterexample: https://dannypsnl.srht.site/math-000X
example : ∃ (X Y : Type) (p : X → X) (f : X → Y), p ≠ id ∧ (fun x => f (p x)) = f := by
  -- Let X = Bool, Y = Unit
  use Bool, Unit
  -- Let p swap true and false, not an identity
  use (fun b => !b)
  -- Let f be the unique function to Unit
  use (fun _ => ())
  constructor
  case h.left =>
    intro h
    have : (fun b => !b) true = id true := by rw [h]
    simp at this
  case h.right =>
    funext x
    rfl
