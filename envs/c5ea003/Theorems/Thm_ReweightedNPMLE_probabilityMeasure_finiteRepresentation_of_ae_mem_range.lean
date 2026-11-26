-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMeasure_finiteRepresentation_of_ae_mem_range
-- name    : ReweightedNPMLE.probabilityMeasure_finiteRepresentation_of_ae_mem_range
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:35.169095+00:00
-- url     : https://prove2.me/theorems/b7902e2d-d018-4e8d-90f8-f133de02a6a2
-- title:
--   Finite representation of a probability measure concentrated on finitely many points
-- statement:
--   Let $\Theta$ be a measurable space in which every singleton is measurable. Fix an injective list $\theta_1,\ldots,\theta_m$ and a probability measure $\mu$ concentrated on its range. Then there are nonnegative real coefficients summing to one such that
--   $$
--   \mu=\sum_{j=1}^{m}p_j\delta_{\theta_j},
--   \qquad p_j\ge0,\qquad \sum_{j=1}^{m}p_j=1.
--   $$
--   Concentration means that $\mu$-almost every point belongs to the listed finite set. No topology on $\Theta$ and no positive lower bound on the coefficients are required.
--
--   This representation allows arguments about arbitrary probability measures concentrated on a finite set to be expressed in finite-dimensional simplex coordinates.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteProbabilityExtreme.lean#L31-L53

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

theorem ReweightedNPMLE.probabilityMeasure_finiteRepresentation_of_ae_mem_range {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (μ : ProbabilityMeasure Θ)
    (hμ : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ) :
    ∃ (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m), finiteProbabilityMeasure θ p hp = μ := by sorry
