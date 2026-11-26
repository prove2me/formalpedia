-- Prove2me | Theorems.Thm_ReweightedNPMLE_mem_gaussianFittedSet_iff_exists_finite_mixture
-- name    : ReweightedNPMLE.mem_gaussianFittedSet_iff_exists_finite_mixture
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:16.224197+00:00
-- url     : https://prove2.me/theorems/310e9aa9-45ec-56ff-8182-72df716fc2bc
-- title:
--   Gaussian fitted vectors are exactly finite probability mixtures of score features
-- statement:
--   Fix finite observations $x_1,\ldots,x_n\in\mathbb R^d$ and any set $K\subset\mathbb R^d$. Define the normalized Gaussian evaluation vector and its fitted set by
--   $$
--   A_x(\theta)_i=\exp\!\left(\langle x_i,\theta\rangle-\|\theta\|_2^2/2\right),
--   \qquad C_x(K)=\operatorname{conv}\{A_x(\theta):\theta\in K\}.
--   $$
--   Then $v\in C_x(K)$ if and only if there are a finite index set $I$, locations $\theta_j\in K$, and weights $p_j\ge0$ with
--   $$
--   \sum_{j\in I}p_j=1,\qquad
--   v=\sum_{j\in I}p_jA_x(\theta_j).
--   $$
--   No compactness or closedness of $K$ is required.
--
--   This identifies the fitted set with actual finite mixtures and provides an exact coefficient representation for subsequent optimization arguments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedGeometry.lean#L71-L96

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
import Definitions.Def_ReweightedNPMLE_FittedGeometry
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

open ReweightedNPMLE

theorem ReweightedNPMLE.mem_gaussianFittedSet_iff_exists_finite_mixture
    {d n : ℕ} (x : Fin n → Point d) (K : Set (Point d))
    (v : Fin n → ℝ) :
    v ∈ gaussianFittedSet x K ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (θ : ι → Point d),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, θ i ∈ K) ∧
          ∑ i, w i • gaussianScoreFeature x (θ i) = v := by sorry
