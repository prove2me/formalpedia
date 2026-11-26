-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_support
-- name    : ReweightedNPMLE.finiteProbabilityMeasure_support
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:37:15.950872+00:00
-- url     : https://prove2.me/theorems/e1dd56f9-a7f8-5934-b5a0-0c7fe0a78ebf
-- title:
--   Exact topological support of a finite mixture with positive coefficients
-- statement:
--   Let $\Theta$ be a $T_1$ topological space equipped with a measurable structure in which every singleton is measurable. Let $\theta_1,\ldots,\theta_m$ be distinct points, and let $p_1,\ldots,p_m$ be strictly positive real numbers whose sum is one. For the probability measure $\mu=\sum_jp_j\delta_{\theta_j}$,
--   $$
--   \operatorname{supp}(\mu)=\{\theta_1,\ldots,\theta_m\}.
--   $$
--   Here support is topological: a point belongs to it when every neighborhood has positive measure.
--
--   The result identifies the represented atoms with the actual support, so a finite representation using distinct locations and positive masses has exactly the intended number of support points.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteProbabilityExtreme.lean#L96-L111

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

theorem ReweightedNPMLE.finiteProbabilityMeasure_support {Θ : Type*}
    [TopologicalSpace Θ] [T1Space Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    {m : ℕ} (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hpPos : ∀ j, 0 < p j) :
    (finiteProbabilityMeasure θ p hp : Measure Θ).support = range θ := by sorry
