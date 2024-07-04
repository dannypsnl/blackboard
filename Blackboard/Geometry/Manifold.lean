import Mathlib.Geometry.Manifold.IntegralCurve
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.MetricSpace.IsometricSMul

open Metric FiniteDimensional Function
open scoped Manifold

variable
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem injective_neg_sphere
  : Injective (fun (x : sphere (0 : E) 1) => -x)
  := by
  exact neg_injective

theorem contMDiff_neg_sphere'
  : ContMDiff (𝓡 n) (𝓡 n) (⊤ : ℕ∞) (fun (x : sphere (0 : E) 1) => -x)
  := by
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp (contMDiff_coe_sphere)

def Hello := EuclideanSpace.instSmoothManifoldWithCornersSphere (E := E) (n := n)

theorem preserves_inner_product_neg_sphere
  (p : sphere (0 : E) 1)
  (d : TangentSpace (𝓡 n) p → TangentSpace (𝓡 n) (-p) :=
    mfderiv (𝓡 n) (𝓡 n) (fun (x : sphere (0 : E) 1) => -x) p)
  (u v : TangentSpace (𝓡 n) p)
  : inner u v = inner (d u) (d v)
  := by
  sorry
