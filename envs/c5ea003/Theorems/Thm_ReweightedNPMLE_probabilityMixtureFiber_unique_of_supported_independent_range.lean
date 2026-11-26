-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_unique_of_supported_independent_range
-- name    : ReweightedNPMLE.probabilityMixtureFiber_unique_of_supported_independent_range
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:27.391096+00:00
-- url     : https://prove2.me/theorems/a4173fab-b3ce-4e1d-a3d3-a2a5eaf4b17d
-- title:
--   Uniqueness within a fitted-value fiber on an independent finite support
-- statement:
--   Let $\Theta$ be a compact topological space whose measurable structure contains every open set and singleton. Let $A:\Theta\to\mathbb R^n$ be continuous, and suppose $A(\theta_1),\ldots,A(\theta_m)$ are linearly independent. Let $\mu,\nu$ be probability measures concentrated on the range of $\theta$ and having the same fitted vector $v$:
--   $$
--   \int_\Theta A\,d\mu=v=\int_\Theta A\,d\nu.
--   $$
--   Then
--   $$
--   \mu=\nu.
--   $$
--   The locations are automatically distinct by linear independence; neither measure is assumed in advance to come with coefficients.
--
--   This establishes uniqueness against arbitrary probability measures on the specified support, extending finite linear-algebra arguments to the full measure-valued fiber.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteProbabilityExtreme.lean#L142-L162

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
import Mathlib.MeasureTheory.Measure.Dirac
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
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.probabilityMixtureFiber_unique_of_supported_independent_range {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ]
    [OpensMeasurableSpace Θ] [MeasurableSingletonClass Θ] {m n : ℕ}
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (θ : Fin m → Θ) (hlin : LinearIndependent ℝ (A ∘ θ))
    (μ ν : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (hν : ν ∈ probabilityMixtureFiber A v)
    (hμS : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ)
    (hνS : ∀ᵐ x ∂(ν : Measure Θ), x ∈ range θ) : μ = ν := by sorry
