import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs

variable
  (𝕜 F : Type*)
  [RCLike 𝕜]
  [AddCommGroup F]
  [Module 𝕜 F]
  [c : InnerProductSpace.Core 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

def toPreInner' : Inner 𝕜 F :=
  c.toInner

attribute [local instance] toPreInner'

theorem vector_eq_iff_inner_product_eq
  (u v : F)
  : u = v ↔ ∀ x, ⟪u, x⟫ = ⟪v, x⟫ := by
  have A : u = v → ∀ x, ⟪u, x⟫ = ⟪v, x⟫ := by
    intros u_eq_v x
    exact congrFun (congrArg (inner 𝕜) u_eq_v) x
  refine Iff.intro A ?reverse
  intros fact
  have fact' := fact u
  have fact'' := fact v
  have P : ⟪u - v, u - v⟫ = ⟪u, u⟫ - ⟪u, v⟫ - ⟪v, u⟫ + ⟪v, v⟫ := by
    exact InnerProductSpace.Core.inner_sub_sub_self u v
  simp [←fact', fact''] at P
  have Q : u - v = 0 := by
    exact InnerProductSpace.Core.inner_self_eq_zero.mp P
  have R : u = v := by
    rw [sub_eq_add_neg] at Q
    have C := eq_neg_of_add_eq_zero_left Q
    rw [neg_neg] at C
    exact C
  exact R
