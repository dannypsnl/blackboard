open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Bool

-- https://g0v.social/@MartinEscardo@mathstodon.xyz/114722727709702521
module escardo-0003 where

variable
  ℓ : Level

we-have : (Σ[ I ∈ Type ℓ ] (I → Type ℓ)) ≃ (Σ[ I ∈ Type ℓ ] (Σ[ Y ∈ Type ℓ ] (I → Y)))
we-have =
  -- f : A -> B
  (λ (I , f) → I , (((i : I) → f i) , λ i0 i1 → {!   !})) ,
  -- isEquiv f
  record {
    equiv-proof = {!   !}
  }
