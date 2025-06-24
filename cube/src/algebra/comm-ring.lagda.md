Import foundation modules and module declaration

```
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

module algebra.comm-ring where
```

now import commutative ring

```
open import Cubical.Algebra.CommRing

variable
  ℓ : Level
```

Proves some very boring

```
module _ (R : CommRing ℓ) where
  open CommRingStr (snd R)

  abstract
    comm-p : (a b : ⟨ R ⟩) → a · b ≡ b · a
    comm-p a b = a · b ≡⟨ ·Comm a b ⟩
                 b · a ∎
```
