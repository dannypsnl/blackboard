```agda
module Semantic where

open import MLTT.Spartan hiding (Type; _∘_)
open import MLTT.List
open import UF.Base hiding (Nat)

_ℕ+_ : ℕ → ℕ → ℕ
zero ℕ+ b = b
succ a ℕ+ b = succ (a ℕ+ b)
```

This is taking from https://gist.github.com/bobatkey/52ea69e8ad83b438c5318346200ab4f0,
"A Quick Introduction to Denotational Semantics using Agda" notes for talk given at TUPLE 2024 (https://typesig.comp-soc.com/tuple/), by Bob Atkey.

What I do here is porting the program but using TypeTopology as library, and add my understanding

## Content

The collection of types

```
data Type : 𝓤₀ ̇  where
  Nat : Type
```

A context is a list of types

```
data Context : 𝓤₀ ̇  where
  ε    : Context
  _▷_ : Context → Type → Context
infix 50 _▷_

variable
  Γ : Context
  T : Type
```

Belongs to context relation

```
data _∋_ : Context → Type → 𝓤₀ ̇  where
  here : ∀ {Γ T}
    --------------
    → Γ ▷ T ∋ T

  there : ∀ {Γ S T} →
    Γ ∋ T
    -------------
    → Γ ▷ S ∋ T
infix 40 _∋_
```

Now let's see the terms with variables in context.
Variable rule says that if we can find `x : T` in the context, then the context can infer the type of `x` is `T`

```
data _⊢_ : Context → Type → 𝓤₀ ̇  where
  var : ∀ {Γ T} → Γ ∋ T
              ---------------
               → Γ ⊢ T
```

Literal rule says that a natural number has type `Nat`

```
  literal : ∀ {Γ} (n : ℕ)
               ---------------
                  → Γ ⊢ Nat
```

Plus rule says that if Γ say `a` and `b` has type `Nat`, then `a + b` this expression (term) has type

```
  _`+_    : ∀ {Γ} → Γ ⊢ Nat
                  → Γ ⊢ Nat
               ---------------
                  → Γ ⊢ Nat
infix 40 _⊢_
```

The standard semantic says

```
module standard-semantics where
```

The type `Nat` is ℕ

```
  ⟦_⟧ty : Type → 𝓤₀ ̇
  ⟦ Nat ⟧ty = ℕ
```

1. An empty context can be view as unit
2. Concat a type with a context can be view as a product

```
  ⟦_⟧ctxt : Context → 𝓤₀ ̇
  ⟦ ε ⟧ctxt     = 𝟙
  ⟦ Γ ▷ T ⟧ctxt = ⟦ Γ ⟧ctxt × ⟦ T ⟧ty
```

1. variable at point takes it out
2. or we ask context about the variable, recursively

```
  ⟦_⟧var : ∀ {Γ T} → Γ ∋ T → ⟦ Γ ⟧ctxt → ⟦ T ⟧ty
  ⟦ here    ⟧var = pr₂
  ⟦ there x ⟧var = λ γ → ⟦ x ⟧var (pr₁ γ)
```

1. A variable term is explained by variable semantic
2. A literal of `n` is just natural number `n`
3. Explaination of `a + b` is addition of natural number

```
  ⟦_⟧term : ∀ {Γ T} → Γ ⊢ T → ⟦ Γ ⟧ctxt → ⟦ T ⟧ty
  ⟦ var x     ⟧term = ⟦ x ⟧var
  ⟦ literal n ⟧term γ = n
  ⟦ t `+ u    ⟧term γ = ⟦ t ⟧term γ ℕ+ ⟦ u ⟧term γ
```

The semantic can be generalized to that

```
record Sem : 𝓤₂ ̇  where
  field
```

we have an Interpretations of types

```
    Obj : 𝓤₁ ̇
```

Interpretations of judgements

```
    _==>_ : Obj → Obj → 𝓤₀ ̇
```

and contexts

```
    Emp   : Obj                 -- Empty context
    _⟨×⟩_ : Obj → Obj → Obj   -- Pairing contexts
```

judgements are composable

```
    -- Composition
    _∘_ : ∀ {X Y Z} → Y ==> Z → X ==> Y → X ==> Z
```

contexts have projection maps

```
    -- Operations on pairs
    project₁ : ∀ {X Y} → (X ⟨×⟩ Y) ==> X
    project₂ : ∀ {X Y} → (X ⟨×⟩ Y) ==> Y
    ⟨_,_⟩ : ∀ {X Y Z} → (X ==> Y) → (X ==> Z) → X ==> (Y ⟨×⟩ Z)
```

Language specific things is that, this langauge has

1. a type `Nat`
2. can take ℕ as literal
3. has an addition for type `Nat`

```
    NatObj       : Obj
    literalArrow : ∀ {X} → ℕ → X ==> NatObj
    addArrow     : (NatObj ⟨×⟩ NatObj) ==> NatObj
```

Interpretation is that, each denotation can be explained by the semantic

```
module Interpretation (𝒜 : Sem) where
  open Sem 𝒜

  ⟦_⟧ty : Type → Obj
  ⟦ Nat ⟧ty = NatObj

  ⟦_⟧ctxt : Context → Obj
  ⟦ ε     ⟧ctxt = Emp
  ⟦ Γ ▷ T ⟧ctxt = ⟦ Γ ⟧ctxt ⟨×⟩ ⟦ T ⟧ty

  ⟦_⟧var : ∀ {Γ T} → Γ ∋ T → ⟦ Γ ⟧ctxt ==> ⟦ T ⟧ty
  ⟦ here    ⟧var = project₂
  ⟦ there x ⟧var = ⟦ x ⟧var ∘ project₁

  ⟦_⟧term : ∀ {Γ T} → Γ ⊢ T → ⟦ Γ ⟧ctxt ==> ⟦ T ⟧ty
  ⟦ var x     ⟧term = ⟦ x ⟧var
  ⟦ literal n ⟧term = literalArrow n
  ⟦ t `+ u    ⟧term = addArrow ∘ ⟨ ⟦ t ⟧term , ⟦ u ⟧term ⟩
```

In this sense let's review standard semantic

```
open Sem

Standard : Sem
Standard .Obj = 𝓤₀ ̇
Standard ._==>_ X Y = X → Y

Standard .Emp = 𝟙
Standard ._⟨×⟩_ = _×_

Standard ._∘_ = λ f g x → f (g x)

Standard .project₁ = pr₁
Standard .project₂ = pr₂
Standard .⟨_,_⟩ = λ f g x → f x , g x

Standard .NatObj = ℕ
Standard .literalArrow n _ = n
Standard .addArrow (m , n) = m ℕ+ n

⟦_⟧standard : ε ▷ Nat ⊢ Nat → ℕ → ℕ
⟦ t ⟧standard n = ⟦ t ⟧term (⋆ , n)
  where open Interpretation Standard
```

A Normalising Semantics (towards presheaves)

Types are now interpreted relative to a context

```
NormType : 𝓤₁ ̇
NormType = Context → 𝓤₀ ̇

NormMor : NormType → NormType → 𝓤₀ ̇
NormMor X Y = ∀ Γ → X Γ → Y Γ

_∘N_ : ∀ {X Y Z} → NormMor Y Z → NormMor X Y → NormMor X Z
f ∘N g = λ Γ z → f Γ (g Γ z)

𝟙N : NormType
𝟙N Γ = 𝟙

_×N_ : NormType → NormType → NormType
(X ×N Y) Γ = X Γ × Y Γ

normProj₁ : ∀ {X Y} → NormMor (X ×N Y) X
normProj₁ = λ Γ → pr₁

normProj₂ : ∀ {X Y} → NormMor (X ×N Y) Y
normProj₂ = λ Γ → pr₂

normPair : ∀ {X Y Z} → NormMor X Y → NormMor X Z → NormMor X (Y ×N Z)
normPair f g = λ Γ z → f Γ z , g Γ z
```

Normalisation

```
NormNat : NormType
NormNat Γ = ℕ × List (Γ ∋ Nat)

normLit : ∀ {X} → ℕ → NormMor X NormNat
normLit n Γ _ = n , []

normAdd : NormMor (NormNat ×N NormNat) NormNat
normAdd Γ ((n₁ , vs₁) , (n₂ , vs₂)) = (n₁ ℕ+ n₂) , (vs₁ ++ vs₂)

NormSem : Sem
NormSem .Obj = NormType
NormSem ._==>_ = NormMor
NormSem .Emp = 𝟙N
NormSem ._⟨×⟩_ = _×N_
NormSem ._∘_ = _∘N_
NormSem .project₁ = normProj₁
NormSem .project₂ = normProj₂
NormSem .⟨_,_⟩ = normPair
NormSem .NatObj = NormNat
NormSem .literalArrow = normLit
NormSem .addArrow = normAdd

normalise : ε ▷ Nat ⊢ Nat → ℕ × List (ε ▷ Nat ∋ Nat)
normalise t = ⟦ t ⟧term (ε ▷ Nat) (⋆ , (0 , [ here ]))
  where open Interpretation NormSem
```
