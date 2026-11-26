-- Prove2me | Theorems.Thm_ReweightedNPMLE_probabilityMixtureFiber_eq_singleton_of_small_extreme_supports
-- name    : ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_small_extreme_supports
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:49:04.653074+00:00
-- url     : https://prove2.me/theorems/a7c52b8e-e369-409b-a362-f06cca09a521
-- title:
--   Small extreme supports and dictionary independence imply full-law uniqueness
-- statement:
--   Let $\Theta$ be compact metric with its Borel structure, $n\ge1$, and $A:\Theta\to\mathbb R^n$ continuous. Let $C$ be convex with $A(\Theta)\subset C\subset(0,\infty)^n$, and let positive weights $w$ have a fitted maximizer $v\in\operatorname{conv}(A(\Theta))$. Suppose $2m\le L$, every injective list of at most $L$ locations gives linearly independent dictionary vectors, and every extreme probability law in the moment fiber has support cardinality at most $m$. Then $$\{\mu\in\mathcal P(\Theta):\int A\,d\mu=v\}=\{\mu_*\}$$ for some extreme law $\mu_*$ with finite topological support of cardinality at most $m$. This yields uniqueness over all mixing laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportUniqueness.lean#L18-L77

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Uniqueness from small extreme supports and evaluation independence

Two extreme laws are concentrated on the union of their finite supports.
Independence on that union forces equality; the full-measure Krein--Milman
theorem then makes the whole optimizer fiber a singleton. This does not assume
finite support of non-extreme optimizing measures.
-/

open Set MeasureTheory
open scoped Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.probabilityMixtureFiber_eq_singleton_of_small_extreme_supports {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n m L : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (hvHull : v ∈ convexHull ℝ (range A)) (hsize : 2 * m ≤ L)
    (hind : ∀ (k : ℕ), k ≤ L → ∀ θ : Fin k → Θ,
      Function.Injective θ → LinearIndependent ℝ (A ∘ θ))
    (hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A v μ →
      (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ ∧ (μ : Measure Θ).support.Finite ∧
        (μ : Measure Θ).support.ncard ≤ m := by sorry
