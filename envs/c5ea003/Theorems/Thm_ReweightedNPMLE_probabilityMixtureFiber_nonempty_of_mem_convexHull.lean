-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_nonempty_of_mem_convexHull
-- name    : ReweightedNPMLE.probabilityMixtureFiber_nonempty_of_mem_convexHull
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:40.715166+00:00
-- url     : https://prove2.me/theorems/9e3e7425-c0f7-551c-9394-2df9cbca1363
-- title:
--   Every convex-hull fitted vector has a probability-law representation
-- statement:
--   Let $\Theta$ be a compact topological space with a measurable structure in which open sets are measurable, and let $A:\Theta\to\mathbb R^n$ be continuous. Write $m_A(\mu)=\int A\,d\mu$ for its coordinatewise moment vector under a probability law $\mu$. If $v\in\operatorname{conv}(A(\Theta))$, then $$\{\mu\in\mathcal P(\Theta):m_A(\mu)=v\}\ne\varnothing.$$ The constructed law can be chosen with finite support. This ensures that fitted-value optimization can be lifted to optimization over all probability measures.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L102-L122

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
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.probabilityMixtureFiber_nonempty_of_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A)) : (probabilityMixtureFiber A v).Nonempty := by sorry
