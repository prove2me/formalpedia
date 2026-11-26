-- Prove2me | Theorems.Thm_ReweightedNPMLE_probability_optimizer_iff_mem_fiber
-- name    : ReweightedNPMLE.probability_optimizer_iff_mem_fiber
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:00.477485+00:00
-- url     : https://prove2.me/theorems/f4063a98-8957-5108-8956-8476993fccad
-- title:
--   Full-law optimizers are exactly the fiber of the unique fitted optimum
-- statement:
--   Let $\Theta$ be a compact topological space with a measurable structure in which open sets are measurable, and let $A:\Theta\to\mathbb R^n$ be continuous. Write $m_A(\mu)=\int A\,d\mu$ for its coordinatewise moment vector under a probability law $\mu$. Write $L_w(v)=\sum_iw_i\log v_i$. Assume $n\ge1$, $C=\operatorname{conv}(A(\Theta))\subset(0,\infty)^n$, $w_i>0$, and $v\in\arg\max_{z\in C}L_w(z)$. For every probability law $\mu$, $$\mu\in\arg\max_{\nu\in\mathcal P(\Theta)}L_w(m_A(\nu))\quad\Longleftrightarrow\quad m_A(\mu)=v.$$ This equivalence separates uniqueness of fitted values from uniqueness of the mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L168-L200

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

theorem ReweightedNPMLE.probability_optimizer_iff_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hCeq : C = convexHull ℝ (range A))
    (hCpos : C ⊆ positiveVectors n)
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (μ : ProbabilityMeasure Θ) :
    IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦ weightedLogLikelihood w (probabilityMixtureValue A ν)) μ ↔
      μ ∈ probabilityMixtureFiber A v := by sorry
