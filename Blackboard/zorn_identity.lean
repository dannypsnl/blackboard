import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Zorn

-- Reading https://golem.ph.utexas.edu/category/2012/10/the_zorn_identity.html
variable [PartialOrder α]
def IsInflationary
  (f : α → α) : Prop :=
  ∀ x, x ≤ (f x)

-- This proof is say (1) => (2)
theorem zorn_fixed_point
  (h : ∀ c : Set α, IsChain LE.le c → ∃ (ub : α), ∀ a ∈ c, a ≤ ub)
  : ∀ f : α → α, IsInflationary f → ∃ k, f k = k
  := by
  intros f f_is_inflationary
  have max := exists_maximal_of_chains_bounded (α := α) (r := LE.le)
    h (fun {a} {b} {c} => Preorder.le_trans a b c)
  let m := max.choose
  exists m
  have left : m ≤ f m := f_is_inflationary m
  have right : f m ≤ m := max.choose_spec (f m) left
  exact le_antisymm right left

-- TODO: how to write this down?
-- theorem zorn_chain
--   (u : ∀ c : Set α, IsChain le c → α)
--   (h : ∀ c : Set α, IsChain le c → ∀ a ∈ c, a ≤ u c)
--   : ∃ c : Set α, IsChain le c → u c ∈ c := by
--   sorry
