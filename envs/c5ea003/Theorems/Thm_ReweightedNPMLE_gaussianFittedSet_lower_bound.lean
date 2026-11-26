-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianFittedSet_lower_bound
-- name    : ReweightedNPMLE.gaussianFittedSet_lower_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:10.262194+00:00
-- url     : https://prove2.me/theorems/3843d44d-bda0-58fb-95b8-31eb98e2c98d
-- title:
--   Uniform positive coordinate bound for the Gaussian fitted set
-- statement:
--   Let $x_1,\ldots,x_n\in\mathbb R^d$, let $K\subset\mathbb R^d$, and suppose $T,S\ge0$ satisfy $\|x_i\|_2\le T$ for every observation and $\|\theta\|_2\le S$ for every $\theta\in K$. Define
--   $$
--   C=\operatorname{conv}\left\{\left(e^{\langle x_i,\theta\rangle-\|\theta\|_2^2/2}\right)_{i=1}^n:\theta\in K\right\}.
--   $$
--   Every $v\in C$ and every coordinate $i$ satisfy
--   $$
--   v_i\ge \exp\!\left(-TS-\frac{S^2}{2}\right).
--   $$
--   No compactness assumption on $K$ is used. Repeated observations and zero values of $S$ or $T$ are allowed.
--
--   The common strictly positive lower bound keeps the fitted-value class away from coordinate singularities of the logarithm.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedGeometry.lean#L193-L215

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

theorem ReweightedNPMLE.gaussianFittedSet_lower_bound {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) (i : Fin n) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤ v i := by sorry
