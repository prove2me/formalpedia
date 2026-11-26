-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedGeometry
-- name    : ReweightedNPMLE_FittedGeometry
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:18:18.319225+00:00
-- url     : https://prove2.me/theorems/19a7ee9a-9bd1-50d6-af4f-ec2238899aab
-- title:
--   Gaussian evaluation features and the fitted-value hull
-- statement:
--   For observations \(x_1,\ldots,x_n\in\mathbb R^d\), define the Gaussian score feature
--   \[
--   A_x(\theta)_i
--   =\exp\!\left(\langle x_i,\theta\rangle-\frac{\|\theta\|^2}{2}\right).
--   \]
--   For a parameter set \(K\subseteq\mathbb R^d\), define the fitted-value class
--   \[
--   C_{x,K}=\operatorname{conv}\{A_x(\theta):\theta\in K\}.
--   \]
--   This is the ordinary convex hull, consisting of finite probability combinations of evaluation vectors. Its coordinates are the Gaussian fitted densities divided by the common centered densities \(\phi_d(x_i)\). The feature map is continuous and strictly positive coordinatewise; when \(K\) is nonempty and compact, the fitted class is likewise nonempty and compact and lies in the positive orthant.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedGeometry.lean#L35-L51

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Compact fitted-value geometry

The infinite-dimensional mixing-law optimization is reduced to the compact
convex hull of the continuous Gaussian evaluation dictionary.  The compact
convex-hull theorem shows this is the actual finite-mixture hull, not merely
its closure, and the Gaussian lower bound keeps it in the positive orthant.
-/

open Set

namespace ReweightedNPMLE



/-- Gaussian evaluation vector after cancellation of the common centered
Gaussian density. -/
noncomputable def gaussianScoreFeature {d n : ℕ}
    (x : Fin n → Point d) (θ : Point d) : Fin n → ℝ :=
  fun i ↦ Real.exp (gaussianScore (x i) θ)

theorem continuous_gaussianScoreFeature {d n : ℕ}
    (x : Fin n → Point d) : Continuous (gaussianScoreFeature x) := by
  apply continuous_pi
  intro i
  unfold gaussianScoreFeature gaussianScore
  fun_prop

/-- Compact convex Gaussian fitted-value class. -/
noncomputable def gaussianFittedSet {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d)) : Set (Fin n → ℝ) :=
  convexHull ℝ (gaussianScoreFeature x '' K)



























end ReweightedNPMLE


