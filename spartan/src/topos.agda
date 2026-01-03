open import MLTT.Spartan
open import UF.SubtypeClassifier
open import UF.FunExt
open import UF.Subsingletons
module topos (fe : Fun-Ext) (pe : Prop-Ext) where

_∧_ : Ω 𝓤 → Ω 𝓤 → Ω 𝓤
a ∧ b = SigmaΩ a (λ _ → b)

-- Follows [SDT2018] Definition 1.12
record topology (𝓤 : Universe) (j : Ω 𝓤 → Ω 𝓤) : 𝓤 ⁺ ̇  where
  field
    respect-true : j ⊤ ＝ ⊤
    idem : (x : Ω 𝓤) → j (j x) ＝ j x
    respect-and : (x y : Ω 𝓤) → j x ∧ j y ＝ j (x ∧ y)

¬¬ : Ω 𝓤 → Ω 𝓤
¬¬ x = not fe (not fe x)

open topology
main : topology 𝓤 ¬¬
main .respect-true = Ω-extensionality pe fe (λ _ → ⋆) λ true not-true → not-true ⋆
main .idem p = Ω-extensionality pe fe three-negations-imply-one ¬¬-intro
main .respect-and p q = Ω-extensionality pe fe und dnu
