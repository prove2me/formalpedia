-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMeasure_positive_finiteRepresentation_of_finite_support
-- name    : ReweightedNPMLE.probabilityMeasure_positive_finiteRepresentation_of_finite_support
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:02.944982+00:00
-- url     : https://prove2.me/theorems/5aaa25ba-6a86-427b-a22e-ee1b86f88266
-- title:
--   Positive atomic representation of a probability measure with finite support
-- statement:
--   Let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $\mu$ be a probability measure whose topological support is finite. There exist $k=\#\operatorname{supp}(\mu)$ distinct locations $\theta_1,\ldots,\theta_k$ and strictly positive coefficients $p_1,\ldots,p_k$ such that
--   $$
--   \{\theta_1,\ldots,\theta_k\}=\operatorname{supp}(\mu),
--   \qquad \sum_{j=1}^k p_j=1,
--   \qquad \mu=\sum_{j=1}^k p_j\delta_{\theta_j}.
--   $$
--   Thus the representation uses every support point exactly once and contains no zero-mass atoms.
--
--   This provides the precise finite representation needed to translate support-cardinality conclusions into linear-algebraic statements about evaluation vectors.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FullExtremeSupport.lean#L117-L151

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

theorem ReweightedNPMLE.probabilityMeasure_positive_finiteRepresentation_of_finite_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : ProbabilityMeasure Θ) (hs : (μ : Measure Θ).support.Finite) :
    ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
      k = (μ : Measure Θ).support.ncard ∧ Function.Injective θ ∧
      range θ = (μ : Measure Θ).support ∧ (∀ j, 0 < p j) ∧ finiteProbabilityMeasure θ p hp = μ := by sorry
