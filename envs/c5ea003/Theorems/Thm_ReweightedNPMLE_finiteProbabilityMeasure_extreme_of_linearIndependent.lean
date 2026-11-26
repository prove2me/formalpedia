-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_extreme_of_linearIndependent
-- name    : ReweightedNPMLE.finiteProbabilityMeasure_extreme_of_linearIndependent
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:41.563581+00:00
-- url     : https://prove2.me/theorems/db3c49f3-665a-5ada-af0c-33eb8c6505ba
-- title:
--   Independent finite mixtures are extreme in the full probability-measure fiber
-- statement:
--   Let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $A:\Theta\to\mathbb R^n$ be continuous. Suppose the vectors $A(\theta_1),\ldots,A(\theta_m)$ are linearly independent. For any nonnegative coefficients $p_j$ summing to one, set
--   $$
--   \mu=\sum_jp_j\delta_{\theta_j},
--   \qquad v=\sum_jp_jA(\theta_j).
--   $$
--   Then $\mu$ is an extreme point of the full fiber
--   $$
--   \mathcal F_v=\left\{\nu\in\mathcal P(\Theta):\int A\,d\nu=v\right\}.
--   $$
--   Zero coefficients are permitted, and no likelihood-optimality assumption is imposed.
--
--   Extremality is tested against decompositions into arbitrary probability measures in $\mathcal F_v$, not merely against coefficient vectors on the chosen finite list.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteProbabilityExtreme.lean#L175-L193

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

theorem ReweightedNPMLE.finiteProbabilityMeasure_extreme_of_linearIndependent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m)
    (hlin : LinearIndependent ℝ (A ∘ θ)) :
    IsExtremeProbabilityMixture A (finiteMixtureValue (A ∘ θ) p) (finiteProbabilityMeasure θ p hp) := by sorry
