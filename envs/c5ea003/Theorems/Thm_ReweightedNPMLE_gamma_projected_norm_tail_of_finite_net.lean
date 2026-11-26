-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_projected_norm_tail_of_finite_net
-- name    : ReweightedNPMLE.gamma_projected_norm_tail_of_finite_net
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:46:32.887785+00:00
-- url     : https://prove2.me/theorems/3ace2394-9f62-5c92-b806-0331c1210da0
-- title:
--   Projected Gamma concentration from a finite directional net
-- statement:
--   Let $\alpha,R>0$, $q\in\mathbb R$, $4R\le\alpha$, and $V\subset\mathbb R^n$. Let a finite set $N$ satisfy $\|v\|_2\le1$ for $v\in N$ and, for every $y\in V$, admit $v\in N\cap V$ with $\|y\|_2\le2\langle v,y\rangle$. Suppose $|N|e^{-R}\le e^{-q}$. For independent $\operatorname{Gamma}(\alpha,\alpha)$ weights, $$\Pr\{\sqrt\alpha\|P_V(W-\mathbf1)\|_2>4\sqrt R\}\le e^{-q}.$$ This turns directional concentration into a norm bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaProjection.lean#L253-L324

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

theorem ReweightedNPMLE.gamma_projected_norm_tail_of_finite_net {n : ℕ} {α R q : ℝ}
    (hα : 0 < α) (hR : 0 < R) (hRα : 4 * R ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (N : Finset (EuclideanSpace ℝ (Fin n)))
    (hNunit : ∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1)
    (hnet : ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y)
    (hcard : (N.card : ℝ) * Real.exp (-R) ≤ Real.exp (-q)) :
    (gammaProductMeasure n α α).real {w |
      4 * Real.sqrt R < Real.sqrt α *
        ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖} ≤
      Real.exp (-q) := by sorry
