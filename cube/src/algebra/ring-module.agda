open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Algebra.CommRing

module algebra.ring-module where

variable
  ℓ : Level

is-compatible : (S : CommRing ℓ) → (V : Type ℓ) → (_∙_ : ⟨ S ⟩ → V → V) → Type ℓ
is-compatible S V _∙_ = {a b : ⟨ S ⟩} {v : V} → a ∙ (b ∙ v) ≡ (a · b) ∙ v
  where open CommRingStr (snd S)

1r-is-neu : (S : CommRing ℓ) → (V : Type ℓ) → (_∙_ : ⟨ S ⟩ → V → V) → Type ℓ
1r-is-neu S V _∙_ = {v : V} → 1r ∙ v ≡ v
  where open CommRingStr (snd S)

is-distrib1 : (S : CommRing ℓ) → (V : Type ℓ) → (_∙_ : ⟨ S ⟩ → V → V) → (_+_ : V → V → V) → Type ℓ
is-distrib1 S V _∙_ _⨁_ = {s : ⟨ S ⟩} {v w : V} → s ∙ (v ⨁ w) ≡ (s ∙ v) ⨁ (s ∙ w)
  where open CommRingStr (snd S)
is-distrib2 : (S : CommRing ℓ) → (V : Type ℓ) → (_∙_ : ⟨ S ⟩ → V → V) → (_+_ : V → V → V) → Type ℓ
is-distrib2 S V _∙_ _⨁_ = {s t : ⟨ S ⟩} {v : V} → (s + t) ∙ v ≡ (s ∙ v) ⨁ (t ∙ v)
  where open CommRingStr (snd S)

record ModuleAxioms (S : CommRing ℓ) (V : Type ℓ) (𝟘 : V) (_+_ : V → V → V) (-_ : V → V) (_∙_ : ⟨ S ⟩ → V → V) : Type ℓ where
  field
    is-setV : isSet V
    +-assoc : {u v w : V} → u + (v + w) ≡ (u + v) + w
    +-comm : {u v : V} → u + v ≡ v + u
    +-neu : {v : V} → 𝟘 + v ≡ v
    +-cancel : {v : V} → v + (- v) ≡ 𝟘
    compatible : is-compatible S V _∙_
    ∙-neu : 1r-is-neu S V _∙_
    distrib1 : is-distrib1 S V _∙_ _+_
    distrib2 : is-distrib2 S V _∙_ _+_

record ModuleStr (R : CommRing ℓ) (V : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    0v         : V
    _⨁_        : V → V → V
    _⨂_        : ⟨ R ⟩ → V → V
    neg        : V → V
    isModule : ModuleAxioms R V 0v _⨁_ neg _⨂_

  infixl 30 _⨂_
  infixl 20 _⨁_

  open ModuleAxioms isModule public

Module : (ℓ : Level) (R : CommRing ℓ) → Type (ℓ-suc ℓ)
Module ℓ R = TypeWithStr ℓ (ModuleStr R)

module _ (R : CommRing ℓ) (V : Module ℓ R) where
  open CommRingStr (snd R)
  open ModuleStr (snd V)

  abstract
    cancelL : (u v w : ⟨ V ⟩) → u ⨁ v ≡ u ⨁ w → v ≡ w
    cancelL u v w P =
      v                  ≡⟨ sym +-neu ⟩
      0v ⨁ v             ≡⟨ cong (_⨁ v) (sym +-cancel) ⟩
      u ⨁ neg u ⨁ v     ≡⟨ cong (_⨁ v) +-comm ⟩
      (neg u) ⨁ u ⨁ v   ≡⟨ sym +-assoc ⟩
      (neg u) ⨁ (u ⨁ v) ≡⟨ cong (neg u ⨁_) P ⟩
      (neg u) ⨁ (u ⨁ w) ≡⟨ +-assoc ⟩
      (neg u) ⨁ u ⨁ w   ≡⟨ cong (_⨁ w) (+-comm ∙ +-cancel) ⟩
      0v ⨁ w             ≡⟨ +-neu ⟩
      w ∎

    scalar-zero : (v : ⟨ V ⟩) → 0r ⨂ v ≡ 0v
    scalar-zero v = cancelL (0r ⨂ v) (0r ⨂ v) 0v (A ∙ B)
      where
      A : (0r ⨂ v) ⨁ (0r ⨂ v) ≡ 0r ⨂ v
      A = (0r ⨂ v) ⨁ (0r ⨂ v) ≡⟨ sym distrib2 ⟩
          (0r + 0r) ⨂ v        ≡⟨ (cong (_⨂ v) (+IdR 0r)) ⟩
          0r ⨂ v ∎
      B : 0r ⨂ v ≡ (0r ⨂ v) ⨁ 0v
      B = 0r ⨂ v        ≡⟨ sym +-neu ⟩
          0v ⨁ (0r ⨂ v) ≡⟨ +-comm ⟩
          (0r ⨂ v) ⨁ 0v ∎
