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
    cancel : {x : G} → (x ⁻¹) ∙ x ＝ e

  infix 40 _⁻¹
  infixl 20 _∙_
```

Wrap the following into private module

```
module _ (G : 𝓤 ̇) where
  open Group {{...}}
```

Now we encounter the first proposition.

## Proposition 1

If $h_1$ and $h_2$ are both inverses of $g$ in the group $G$, then $h_1 = h_2$.

```
  propopsition-1 : {{_ : Group G}} {g h1 h2 : G} → (g ∙ h1 ＝ e) → (g ∙ h2 ＝ e) → h1 ＝ h2
  propopsition-1 {g}{h1}{h2} fact1 fact2 =
    h1 ＝⟨ sym (neu-l h1) ⟩
    e ∙ h1 ＝⟨ ap (_∙ h1) (sym cancel) ⟩
    g ⁻¹ ∙ g ∙ h1 ＝⟨ ∙-assoc (g ⁻¹) g h1 ⟩
    g ⁻¹ ∙ (g ∙ h1) ＝⟨ ap ((g ⁻¹) ∙_) fact1 ⟩
    g ⁻¹ ∙ e ＝⟨ ap ((g ⁻¹) ∙_) (sym fact2) ⟩
    g ⁻¹ ∙ (g ∙ h2) ＝⟨ sym (∙-assoc (g ⁻¹) g h2) ⟩
    g ⁻¹ ∙ g ∙ h2 ＝⟨ ap (_∙ h2) cancel ⟩
    e ∙ h2 ＝⟨ neu-l h2 ⟩
    h2 ∎
```
