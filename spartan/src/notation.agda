module notation where

open import MLTT.Spartan
open import UF.Sets

record GroupStructure (G : 𝓤 ̇) : 𝓤 ̇ where
  field
    mul : G → G → G
    e : G
    inv : G → G

record GroupAxiom {G : 𝓤 ̇} (str : GroupStructure G) : 𝓤 ̇ where
  open GroupStructure str
  field
    size : is-set G
    ∙-assoc : associative mul
    neuL : left-neutral e mul
    neuR : right-neutral e mul
    invL : {x : G} → (mul (inv x) x ＝ e)
    invR : {x : G} → (mul x (inv x) ＝ e)

record CommGroupAxiom {G : 𝓤 ̇} (str : GroupStructure G) : 𝓤 ̇ where
  open GroupStructure str
  field
    ax : GroupAxiom str
    commute : commutative mul

CommGroup : (𝓤 : Universe) → 𝓤 ⁺  ̇
CommGroup 𝓤 = Σ G ꞉ 𝓤 ̇ , Σ str ꞉ GroupStructure G , CommGroupAxiom str

module Notation where
  ⟨_⟩ : {S : 𝓤 ̇ → 𝓥 ̇ } → Σ S → 𝓤 ̇
  ⟨ X , s ⟩ = X

  module AddGroup (A : CommGroup 𝓤) where
    open GroupStructure (A .pr₂ .pr₁)
    _+ₐ_ = mul
    -_ = inv
    0a = e

    infix 40 -_
    infixl 20 _+ₐ_

module _ (A : CommGroup 𝓤) where
  open Notation
  open Notation.AddGroup A
  open CommGroupAxiom (A .pr₂ .pr₂)
  open GroupAxiom (CommGroupAxiom.ax (A .pr₂ .pr₂))

  propopsition-1 : {h : ⟨ A ⟩} → h +ₐ - h ＝ 0a +ₐ 0a
  propopsition-1 {h} =
    h +ₐ - h ＝⟨ invR ⟩
    0a ＝⟨ neuL 0a ⁻¹ ⟩
    0a +ₐ 0a ∎
