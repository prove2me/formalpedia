-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation
-- name    : ReweightedNPMLE.probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:42.828638+00:00
-- url     : https://prove2.me/theorems/44e47420-94a5-578a-a5cd-273de094672d
-- title:
--   A nonzero bounded zero-moment perturbation excludes extremality
-- statement:
--   Let $n\ge0$, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $A:\Theta\to\mathbb R^n$ be continuous. For $v\in\mathbb R^n$, define its probability-mixture fiber by
--   $$
--   \mathcal F_A(v)=\left\{\mu\in\mathcal P(\Theta):\int_\Theta A(a)\,d\mu(a)=v\right\}.
--   $$
--   Extreme points refer to the full fiber of probability measures, not only to a finite dictionary of atoms.
--
--   Let $\mu\in\mathcal F_A(v)$. Suppose $h:\Theta\to\mathbb R$ is measurable and satisfies
--   $$
--   |h(a)|\le\tfrac12\quad(a\in\Theta),\qquad
--   \int h\,d\mu=0,\qquad
--   \int h(a)A_i(a)\,d\mu(a)=0\quad(i=1,\ldots,n).
--   $$
--   Assume $h$ is not zero $\mu$-almost everywhere. Then
--   $$
--   \mu\notin\operatorname{ext}\mathcal F_A(v).
--   $$
--
--   This perturbation criterion is the measure-theoretic mechanism behind finite-support characterizations of extreme mixture laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MeasureFiberPerturbation.lean#L37-L126

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Moment-preserving perturbations of probability measures

A bounded nonzero perturbation with zero mass and zero fitted moments gives
two genuine probability measures in the same full fiber whose average is
the original law. This applies to arbitrary, possibly infinite-support laws.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.probabilityMixtureFiber_not_extreme_of_bounded_zero_moment_perturbation {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (h : Θ → ℝ) (hhmeas : Measurable h) (hhbound : ∀ x, |h x| ≤ 1 / 2)
    (hhmean : ∫ x, h x ∂μ = 0)
    (hhmoment : ∀ i, ∫ x, h x * A x i ∂μ = 0)
    (hhnonzero : ¬ h =ᵐ[(μ : Measure Θ)] fun _ ↦ 0) :
    ¬ IsExtremeProbabilityMixture A v μ := by sorry
