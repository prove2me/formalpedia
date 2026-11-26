-- Prove2me | Theorems.Thm_ReweightedNPMLE_full_probability_optimizer_extreme_iff
-- name    : ReweightedNPMLE.full_probability_optimizer_extreme_iff
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:45.621491+00:00
-- url     : https://prove2.me/theorems/506d27f7-ed08-4c16-baf5-67a24367465f
-- title:
--   Complete finite-support characterization of full probability-measure extreme optimizers
-- statement:
--   Let $\Theta$ be a compact metric Borel space, $n\ge1$, and $A:\Theta\to\mathbb R^n$ continuous. Let $C\subset(0,\infty)^n$ be convex with $A(\Theta)\subset C$, and suppose $v$ maximizes $\sum_iw_i\log u_i$ over $C$ for strictly positive weights. For any $\mu\in\mathcal P(\Theta)$, membership as an extreme point of the fiber $\{\nu:\int A\,d\nu=v\}$ is equivalent to the existence of distinct locations $\theta_1,\ldots,\theta_k$, with $k\le n$, and positive coefficients satisfying
--   $$
--   \sum_jp_j=1,\qquad
--   \mu=\sum_jp_j\delta_{\theta_j},\qquad
--   \sum_jp_jA(\theta_j)=v,
--   $$
--   where the vectors $A(\theta_j)$ are linearly independent.
--
--   The characterization derives finite support and the $n$-atom bound from full-fiber extremality; it does not assume an atomic optimization domain.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FullExtremeSupport.lean#L153-L191

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

theorem ReweightedNPMLE.full_probability_optimizer_extreme_iff {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔
      ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
        k ≤ n ∧ Function.Injective θ ∧ (∀ j, 0 < p j) ∧ LinearIndependent ℝ (A ∘ θ) ∧
          finiteMixtureValue (A ∘ θ) p = v ∧ finiteProbabilityMeasure θ p hp = μ := by sorry
