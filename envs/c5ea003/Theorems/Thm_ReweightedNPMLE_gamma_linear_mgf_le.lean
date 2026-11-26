-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_linear_mgf_le
-- name    : ReweightedNPMLE.gamma_linear_mgf_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:16.073803+00:00
-- url     : https://prove2.me/theorems/fcac75bf-3b5b-49f6-ac27-73f71adae5a2
-- title:
--   Moment bound for normalized linear combinations of Gamma weights
-- statement:
--   Let $W_i$ be independent $\operatorname{Gamma}(\alpha,\alpha)$ variables, $\alpha>0$, and $v\in\mathbb R^n$ satisfy $\sum_i v_i^2\le1$. For $|\lambda|\le\sqrt\alpha/2$, $$\mathbb E\exp\!\left(\lambda\sqrt\alpha\sum_i v_i(W_i-1)\right)\le e^{\lambda^2}.$$ This provides the directional concentration estimate needed to control a subspace projection.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaProjection.lean#L91-L166

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.gamma_linear_mgf_le {n : ℕ} {α lam : ℝ} (hα : 0 < α)
    (hlam : |lam| ≤ Real.sqrt α / 2) (v : Fin n → ℝ)
    (hv : ∑ i, v i ^ 2 ≤ 1) :
    ∫ w, Real.exp (lam * Real.sqrt α * ∑ i, v i * (w i - 1))
        ∂gammaProductMeasure n α α ≤ Real.exp (lam ^ 2) := by sorry
