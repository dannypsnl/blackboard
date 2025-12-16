module em where

open import MLTT.Spartan

¬¬em : {P : 𝓤 ̇} → ((P + (P → 𝟘 {𝓤})) → 𝟘 {𝓤}) → 𝟘 {𝓤}
¬¬em x = x (inr λ p → x (inl p))
