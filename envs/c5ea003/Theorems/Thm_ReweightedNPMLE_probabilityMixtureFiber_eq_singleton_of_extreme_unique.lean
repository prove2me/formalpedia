-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_eq_singleton_of_extreme_unique
-- name    : ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_extreme_unique
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:05.124925+00:00
-- url     : https://prove2.me/theorems/46a1f4c0-d3e0-4057-9e12-90865bc16472
-- title:
--   Uniqueness of extreme laws forces the entire probability fiber to be a singleton
-- statement:
--   Let $n\ge0$, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $A:\Theta\to\mathbb R^n$ be continuous. For $v\in\mathbb R^n$, define its probability-mixture fiber by
--   $$
--   \mathcal F_A(v)=\left\{\mu\in\mathcal P(\Theta):\int_\Theta A(a)\,d\mu(a)=v\right\}.
--   $$
--   Extreme points refer to the full fiber of probability measures, not only to a finite dictionary of atoms.
--
--   Suppose $v\in\operatorname{conv}(A(\Theta))$ and that every pair of extreme laws in $\mathcal F_A(v)$ is equal. Then there exists $\mu\in\mathcal P(\Theta)$ such that
--   $$
--   \mathcal F_A(v)=\{\mu\},\qquad
--   \mu\in\operatorname{ext}\mathcal F_A(v).
--   $$
--   No finite-support assumption is imposed on the members of the fiber.
--
--   This is the full probability-measure uniqueness step: proving uniqueness only among extreme solutions suffices to prove uniqueness among all mixing laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityFiberGeometry.lean#L139-L170

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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_extreme_unique {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A))
    (hunique : ∀ μ ν : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture A v μ → IsExtremeProbabilityMixture A v ν → μ = ν) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ := by sorry
