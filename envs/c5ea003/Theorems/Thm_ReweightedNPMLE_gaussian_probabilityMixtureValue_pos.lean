-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussian_probabilityMixtureValue_pos
-- name    : ReweightedNPMLE.gaussian_probabilityMixtureValue_pos
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:36.772059+00:00
-- url     : https://prove2.me/theorems/2a4cddbe-a306-4eaf-afb9-5c228449e718
-- title:
--   Strict positivity of Gaussian probability-mixture fitted values
-- statement:
--   Let $d,n\ge0$ be integers, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous. With $\varphi_d$ denoting the standard Gaussian density, define
--   $$
--   f_\mu(x)=\int_\Theta\varphi_d(x-\theta(a))\,d\mu(a)
--   \qquad(\mu\in\mathcal P(\Theta)).
--   $$
--
--   Assume $\Theta$ is nonempty. For every probability law $\mu$ on $\Theta$, every data vector $(x_1,\ldots,x_n)$, and each sample coordinate $i$,
--   $$
--   f_\mu(x_i)>0.
--   $$
--
--   Strict positivity ensures that fitted Gaussian log-likelihoods and log-density ratios are well defined throughout the probability-measure parameter space.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ParameterizedProbabilityIntegral.lean#L87-L103

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

theorem ReweightedNPMLE.gaussian_probabilityMixtureValue_pos {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (μ : ProbabilityMeasure Θ) (i : Fin n) :
    0 < probabilityMixtureValue (fun a j ↦ gaussianKernel d (x j) (θ a)) μ i := by sorry
