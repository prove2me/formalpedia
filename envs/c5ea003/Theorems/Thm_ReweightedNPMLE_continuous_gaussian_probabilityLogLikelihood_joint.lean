-- Prove2me | Theorems.Thm_ReweightedNPMLE_continuous_gaussian_probabilityLogLikelihood_joint
-- name    : ReweightedNPMLE.continuous_gaussian_probabilityLogLikelihood_joint
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:55.851805+00:00
-- url     : https://prove2.me/theorems/24440db4-95ec-48da-aa78-b03deb94fb7d
-- title:
--   Joint continuity of Gaussian mixture log-likelihood in data, weights, and law
-- statement:
--   Let $d,n\ge0$ be integers, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous. With $\varphi_d$ denoting the standard Gaussian density, define
--   $$
--   f_\mu(x)=\int_\Theta\varphi_d(x-\theta(a))\,d\mu(a)
--   \qquad(\mu\in\mathcal P(\Theta)).
--   $$
--
--   Assume $\Theta$ is nonempty. For arbitrary real weights $w\in\mathbb R^n$, the map
--   $$
--   (x,w,\mu)\longmapsto\sum_{i=1}^n w_i\log f_\mu(x_i)
--   $$
--   is jointly continuous in the Euclidean data and weight variables and the weak topology on $\mathcal P(\Theta)$. The weights need not be positive.
--
--   This continuity is the analytic foundation for closed optimizer-comparison graphs and Borel failure events in the conditional-to-joint arguments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ParameterizedProbabilityIntegral.lean#L105-L125

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Joint continuity of compact-parameter probability integrals

Weak convergence of the law and uniform convergence of the integrand can
vary simultaneously. The probability normalization bounds the integral of
the varying integrand difference by its supremum norm.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.continuous_gaussian_probabilityLogLikelihood_joint {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (fun p : ((Fin n → Point d) × (Fin n → ℝ)) × ProbabilityMeasure Θ ↦
      weightedLogLikelihood p.1.2
        (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)) := by sorry
