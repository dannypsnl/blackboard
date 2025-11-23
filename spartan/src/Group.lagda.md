# Group

Module

```agda
module Group where

open import MLTT.Spartan hiding (_∙_) renaming (_⁻¹ to sym)
open import UF.Base
open import UF.Sets
open import UF.Sets-Properties
```

Definition

```agda
record Group (G : 𝓤 ̇) : 𝓤 ̇ where
  field
    size : is-set G
    _∙_ : G → G → G
    ∙-assoc : associative _∙_
    e : G
    neu-l : left-neutral e _∙_
    neu-r : right-neutral e _∙_
    _⁻¹ : G → G
    cancel : {x : G} → ((x ⁻¹) ∙ x ＝ e) × (x ∙ (x ⁻¹) ＝ e)

  infix 40 _⁻¹
  infixl 20 _∙_
```

Wrap the following into private module

```
module _ (G : 𝓤 ̇) where
  open Group {{...}}
```

Now we encounter some propositions.

## Proposition 1

The purpose of this proposition is to tell the identity is unique, so if $h$ is another identity (in fact, this condition can be refined as below), then $h = e$.

```
  propopsition-1 : {{_ : Group G}} {h : G} → left-neutral h _∙_ → h ＝ e
  propopsition-1 {h} h-is-identity =
    h ＝⟨ sym (neu-r h) ⟩
    h ∙ e ＝⟨ h-is-identity e ⟩
    e ∎
```

## Proposition 2

If $h_1$ and $h_2$ are both inverses of $g$ in the group $G$, then $h_1 = h_2$.

```
  propopsition-2 : {{_ : Group G}} {g h1 h2 : G} → (g ∙ h1 ＝ e) → (g ∙ h2 ＝ e) → h1 ＝ h2
  propopsition-2 {g}{h1}{h2} fact1 fact2 =
    h1 ＝⟨ sym (neu-l h1) ⟩
    e ∙ h1 ＝⟨ ap (_∙ h1) (sym (cancel .pr₁)) ⟩
    g ⁻¹ ∙ g ∙ h1 ＝⟨ ∙-assoc (g ⁻¹) g h1 ⟩
    g ⁻¹ ∙ (g ∙ h1) ＝⟨ ap ((g ⁻¹) ∙_) fact1 ⟩
    g ⁻¹ ∙ e ＝⟨ ap ((g ⁻¹) ∙_) (sym fact2) ⟩
    g ⁻¹ ∙ (g ∙ h2) ＝⟨ sym (∙-assoc (g ⁻¹) g h2) ⟩
    g ⁻¹ ∙ g ∙ h2 ＝⟨ ap (_∙ h2) (cancel .pr₁) ⟩
    e ∙ h2 ＝⟨ neu-l h2 ⟩
    h2 ∎
```

## Proposition 3

Every element of group is cancellable.

```
  propopsition-3 : {{_ : Group G}} {g h a : G} → (g ∙ a ＝ h ∙ a → g ＝ h) × (a ∙ g ＝ a ∙ h → g ＝ h)
  propopsition-3 {g}{h}{a} = I , II
    where
    I : g ∙ a ＝ h ∙ a → g ＝ h
    I fact =
      g ＝⟨ sym (neu-r g) ⟩
      g ∙ e ＝⟨ ap (g ∙_) (sym (cancel .pr₂)) ⟩
      g ∙ (a ∙ a ⁻¹) ＝⟨ sym (∙-assoc g a (a ⁻¹)) ⟩
      g ∙ a ∙ a ⁻¹ ＝⟨ ap (_∙ a ⁻¹) fact ⟩
      h ∙ a ∙ a ⁻¹ ＝⟨ ∙-assoc h a (a ⁻¹) ⟩
      h ∙ (a ∙ a ⁻¹) ＝⟨ ap (h ∙_) (cancel .pr₂) ⟩
      h ∙ e ＝⟨ neu-r h ⟩
      h ∎

    II : a ∙ g ＝ a ∙ h → g ＝ h
    II fact =
      g ＝⟨ sym (neu-l g) ⟩
      e ∙ g ＝⟨ ap (_∙ g) (sym (cancel .pr₁)) ⟩
      a ⁻¹ ∙ a ∙ g ＝⟨ ∙-assoc (a ⁻¹) a g ⟩
      a ⁻¹ ∙ (a ∙ g) ＝⟨ ap ((a ⁻¹) ∙_) fact ⟩
      a ⁻¹ ∙ (a ∙ h) ＝⟨ sym (∙-assoc (a ⁻¹) a h) ⟩
      a ⁻¹ ∙ a ∙ h ＝⟨ ap (_∙ h) (cancel .pr₁) ⟩
      e ∙ h ＝⟨ neu-l h ⟩
      h ∎
```
