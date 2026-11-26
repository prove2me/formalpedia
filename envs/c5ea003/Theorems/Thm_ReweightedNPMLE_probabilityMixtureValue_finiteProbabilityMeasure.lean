-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure
-- name    : ReweightedNPMLE.probabilityMixtureValue_finiteProbabilityMeasure
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:36.307469+00:00
-- url     : https://prove2.me/theorems/3a82d182-b180-457e-8828-f849c6a64e0f
-- title:
--   Moment vector of a finite atomic probability law
-- statement:
--   Let $\Theta$ be a compact topological space with a measurable structure in which open sets are measurable, and let $A:\Theta\to\mathbb R^n$ be continuous. Write $m_A(\mu)=\int A\,d\mu$ for its coordinatewise moment vector under a probability law $\mu$. Let $\theta_1,\ldots,\theta_m\in\Theta$ and let $p_j\ge0$ sum to one. For $\mu=\sum_jp_j\delta_{\theta_j}$, $$m_A(\mu)=\sum_{j=1}^m p_jA(\theta_j).$$ Locations need not be distinct. This identifies full-law moments with the finite coefficient representation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L81-L100

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

theorem ReweightedNPMLE.probabilityMixtureValue_finiteProbabilityMeasure {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    probabilityMixtureValue A (finiteProbabilityMeasure θ p hp) =
      finiteMixtureValue (A ∘ θ) p := by sorry
