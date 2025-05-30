import Mathlib.Order.Defs.PartialOrder

class Poset (α : Type u) extends (Preorder α) where
  antisymm : {p q : α} → p ≤ q ∧ q ≤ p → p = q

@[simp] lemma antisymm [Poset α] : ∀ {p q : α}, p ≤ q ∧ q ≤ p → p = q := Poset.antisymm

def SemiDirected [Poset P] (a : I → P)
  : Prop :=
  ∃ k : I, ∀ i j : I, (a i) ≤ (a k) ∧ (a j) ≤ (a k)

def UpperBound [Poset P] (x : P) (a : I → P) : Prop :=
  ∀ i : I, a i ≤ x

def LUB [Poset P] (x : P) (a : I → P) : Prop :=
  UpperBound x a ∧ ∀ y, UpperBound y a → x ≤ y

theorem LUB_uniqueness
  [Poset P]
  (a : I → P)
  (P : LUB x a)
  (Q : LUB y a)
  : x = y := by
  have one := P.left
  have two := Q.right x one
  have three := Q.left
  have four := P.right y three
  exact antisymm ⟨ four , two ⟩
