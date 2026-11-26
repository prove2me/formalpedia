-- Prove2me | Theorems.Thm_ReweightedNPMLE_probability_optimizer_not_extreme_of_disjoint_positive_regions
-- name    : ReweightedNPMLE.probability_optimizer_not_extreme_of_disjoint_positive_regions
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:38:54.788216+00:00
-- url     : https://prove2.me/theorems/442086ac-7630-42f4-8e20-21695bde6b2a
-- title:
--   More than n disjoint positive-mass regions prevent an extreme optimizer
-- statement:
--   Let $\Theta$ be compact metric, $A:\Theta\to\mathbb R^n$ continuous, and $n\ge1$. Suppose $A(\Theta)$ lies in a convex set $C\subset(0,\infty)^n$, and $v$ maximizes $\sum_iw_i\log v_i$ over $C$ for positive weights $w$. Let $\mu$ be a probability measure with $\int A\,d\mu=v$. If there are $m>n$ pairwise disjoint measurable regions $E_1,\ldots,E_m$, each having positive $\mu$-mass, then $\mu$ is not an extreme point of the probability-measure fiber $\{\nu:\int A\,d\nu=v\}$. The regions need not cover the parameter space, and no atomicity is assumed.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ExtremeSupportPartition.lean#L47-L136

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
# Too many disjoint positive-mass regions prevent extremality

The contact identity converts zero fitted moments into zero mass. A finite
linear dependence among restricted evaluation moments gives a bounded
nonzero perturbation, hence a nontrivial decomposition of the full optimizer.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.probability_optimizer_not_extreme_of_disjoint_positive_regions {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n < m)
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (E : Fin m → Set Θ) (hE : ∀ j, MeasurableSet (E j))
    (hEd : Pairwise (fun j k ↦ Disjoint (E j) (E k))) (hEpos : ∀ j, 0 < (μ : Measure Θ) (E j)) :
    ¬ IsExtremeProbabilityMixture A v μ := by sorry
