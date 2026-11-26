-- Prove2me | Theorems.Thm_ReweightedNPMLE_full_extreme_optimizer_support_finite_card_le
-- name    : ReweightedNPMLE.full_extreme_optimizer_support_finite_card_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:19.516796+00:00
-- url     : https://prove2.me/theorems/8a962c55-457d-5e78-beb3-2b855e6040cb
-- title:
--   Every extreme probability-measure optimizer has at most $n$ support points
-- statement:
--   Let $\Theta$ be a compact metric Borel space, $n\ge1$, and $A:\Theta\to\mathbb R^n$ continuous. Let $C\subset(0,\infty)^n$ be convex with $A(\Theta)\subset C$. Suppose $w_i>0$ and $v\in C$ maximizes $L_w(u)=\sum_iw_i\log u_i$ over $C$. If $\mu$ is an extreme point of the full fiber $\{\nu\in\mathcal P(\Theta):\int A\,d\nu=v\}$, then
--   $$
--   \operatorname{supp}(\mu)\text{ is finite},
--   \qquad \#\operatorname{supp}(\mu)\le n.
--   $$
--   Finiteness of the topological support is a conclusion, not a hypothesis.
--
--   The bound controls every full-fiber extreme optimizer, including measures initially allowed to have infinitely many support points.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FullExtremeSupport.lean#L70-L102

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
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
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
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.full_extreme_optimizer_support_finite_card_le {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A v μ) :
    (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ n := by sorry
