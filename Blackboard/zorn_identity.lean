import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Defs

-- Reading https://golem.ph.utexas.edu/category/2012/10/the_zorn_identity.html
variable [PartialOrder α]

def IsInflationary (f : α → α) : Prop :=
  ∀ x, x ≤ (f x)

def IsMaximal (m : α) : Prop := ∀ x : α, m ≤ x → x ≤ m

-- Here proves (1) => (2)
theorem zorn_fixed_point
  (h : ∀ c : Set α, IsChain LE.le c → ∃ (ub : α), ∀ a ∈ c, a ≤ ub)
  : ∀ f : α → α, IsInflationary f → ∃ k, f k = k
  := by
  intros f f_is_inflationary
  -- use `exists_maximal_of_chains_bounded` from mathlib4
  have max := exists_maximal_of_chains_bounded (α := α) (r := LE.le)
    h (fun {a} {b} {c} => Preorder.le_trans a b c)
  let m := max.choose
  exists m
  have left : m ≤ f m := f_is_inflationary m
  have right : f m ≤ m := max.choose_spec (f m) left
  exact le_antisymm right left

-- A more general version is defined in Mathlib.Order.Zorn called `exists_maximal_of_chains_bounded`
theorem zorn_maximal
  (h : ∀ c : Set α, IsChain LE.le c → ∃ (ub : α), ∀ a ∈ c, a ≤ ub)
  (p : ∃ s : α → α,
    IsInflationary s ∧ (∀ x : α, s x = x → IsMaximal x))
  : ∃ (m : α), IsMaximal m := by
  -- Here proves (2) => (1)
  let s := Classical.choose p
  have many := Classical.choose_spec p
  have s_is_inflationary := many.left
  have second := zorn_fixed_point h s s_is_inflationary
  let k := second.choose
  exists k
  have : s k = k := second.choose_spec
  exact many.right k this
