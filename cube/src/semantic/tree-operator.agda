-- https://treecalcul.us/specification/
module semantic.tree-operator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

data E : Type where
  t : E
  _·_ : E → E → E
infixl 5 _·_

infix 4 _—→_
data _—→_ : E → E → Type where
  r1 : ∀ (a b : E)
      → t · t · a · b —→ a
  r2 : ∀ (a b c : E)
      → t · (t · a) · b · c —→ a · c · (b · c)
  r3a : ∀ (a b c : E)
        → t · (t · a · b) · c · t —→ a
  r3b : ∀ (a b c u : E)
        → t · (t · a · b) · c · (t · u) —→ b · u
  r3c : ∀ (a b c u v : E)
        → t · (t · a · b) · c · (t · u · v) —→ c · u · v
  _⨾_ : {a b c : E}
        → a —→ b
        → b —→ c
        → a —→ c
infixl 15 _⨾_

false = t
true = t · t
not = t · (t · (t · t) · (t · t · t)) · t

test₁ : not · false —→ true
test₁ = r3a (t · t) (t · t · t) t

test₂ : not · true —→ false
test₂ = s1 ⨾ s2
  where s1 : not · true —→ t · t · t · t
        s1 = r3b (t · t) (t · t · t) t t
        s2 : t · t · t · t —→ false
        s2 = r1 t t
