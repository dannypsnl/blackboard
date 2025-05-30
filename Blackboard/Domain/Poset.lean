import Mathlib.Order.Defs.PartialOrder

class Poset (α : Type u) extends (Preorder α) where
  antisymm : {p q : α} → p ≤ q ∧ q ≤ p → p = q

@[simp] lemma antisymm [Poset α] : ∀ {p q : α}, p ≤ q ∧ q ≤ p → p = q := Poset.antisymm

def SemiDirected [Poset P] (a : I → P)
  : Prop :=
  ∃ k : I, ∀ i j : I, (a i) ≤ (a k) ∧ (a j) ≤ (a k)

def UpperBound [Poset P] (x : P) (a : I → P) : Prop :=
  ∀ i : I, a i ≤ x
