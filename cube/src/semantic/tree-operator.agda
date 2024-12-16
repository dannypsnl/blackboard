-- https://treecalcul.us/specification/
module semantic.tree-operator where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

data E : Type where
  Δ : E
  _·_ : E → E → E
infixl 5 _·_

infix 4 _—→_
data _—→_ : E → E → Type where
  r1 : ∀ (a b : E)
      → Δ · Δ · a · b —→ a
  r2 : ∀ (a b c : E)
      → Δ · (Δ · a) · b · c —→ a · c · (b · c)
  r3a : ∀ (a b c : E)
        → Δ · (Δ · a · b) · c · Δ —→ a
  r3b : ∀ (a b c u : E)
        → Δ · (Δ · a · b) · c · (Δ · u) —→ b · u
  r3c : ∀ (a b c u v : E)
        → Δ · (Δ · a · b) · c · (Δ · u · v) —→ c · u · v
  _⨾_ : {a b c : E}
        → a —→ b
        → b —→ c
        → a —→ c
infixl 15 _⨾_

false = Δ
true = Δ · Δ
not = Δ · (Δ · (Δ · Δ) · (Δ · Δ · Δ)) · Δ
id = Δ · (Δ · Δ · Δ) · Δ

test₁ : not · false —→ true
test₁ = r3a (Δ · Δ) (Δ · Δ · Δ) Δ

test₂ : not · true —→ false
test₂ = s1 ⨾ s2
  where s1 : not · true —→ Δ · Δ · Δ · Δ
        s1 = r3b (Δ · Δ) (Δ · Δ · Δ) Δ Δ 
        s2 : Δ · Δ · Δ · Δ —→ false
        s2 = r1 Δ Δ

test₃ : id · false —→ false
test₃ = r3a Δ Δ Δ
