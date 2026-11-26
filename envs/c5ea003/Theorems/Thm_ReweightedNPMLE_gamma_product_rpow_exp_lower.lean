-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_product_rpow_exp_lower
-- name    : ReweightedNPMLE.gamma_product_rpow_exp_lower
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:49.269386+00:00
-- url     : https://prove2.me/theorems/0a70005b-f58b-52f6-9d4d-bbbd1da8711d
-- title:
--   Exponential lower bound for multiplicative Gamma factors
-- statement:
--   Let $\alpha\ge0$ and let $w,t\in\mathbb R^n$ satisfy $|t_i|\le1/8$ for every coordinate. Then
--   $$
--   \exp\!\left[-\alpha\left\{\sum_i(w_i-1)t_i+\sum_i t_i^2\right\}\right]
--   \le
--   \left\{\prod_i(1+t_i)^\alpha\right\}
--   \exp\!\left(-\alpha\sum_iw_it_i\right).
--   $$
--   The vector $w$ is arbitrary; this algebraic inequality does not require positive weights or a probability model. The restriction on $t$ ensures $1+t_i>0$, so every real power is well defined by the usual positive-base convention. The inequality supplies a quadratic exponential bound for the multiplicative factors in a Gamma density ratio.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ChangeOfVariables.lean#L21-L53

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.gamma_product_rpow_exp_lower {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (w t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 8) :
    Real.exp (-α * (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2)) ≤
      (∏ i, (1 + t i) ^ α) * Real.exp (-α * ∑ i, w i * t i) := by sorry
