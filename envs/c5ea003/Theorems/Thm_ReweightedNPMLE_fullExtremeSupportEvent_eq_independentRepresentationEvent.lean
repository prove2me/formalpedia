-- Prove2me | Theorems.Thm_ReweightedNPMLE_fullExtremeSupportEvent_eq_independentRepresentationEvent
-- name    : ReweightedNPMLE.fullExtremeSupportEvent_eq_independentRepresentationEvent
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:11.845086+00:00
-- url     : https://prove2.me/theorems/a38c40ce-5d0f-5177-9f7f-507c49ceb008
-- title:
--   Extreme-law support sizes equal independent fitted-representation sizes
-- statement:
--   Let $n\ge0$, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $A:\Theta\to\mathbb R^n$ be continuous. For $v\in\mathbb R^n$, define its probability-mixture fiber by
--   $$
--   \mathcal F_A(v)=\left\{\mu\in\mathcal P(\Theta):\int_\Theta A(a)\,d\mu(a)=v\right\}.
--   $$
--   Extreme points refer to the full fiber of probability measures, not only to a finite dictionary of atoms.
--
--   Assume $n\ge1$. Let $C\subseteq(0,\infty)^n$ be convex with $A(\Theta)\subseteq C$, and let $\widehat v(w)$ maximize $\ell_w$ on $C$ for every strictly positive weight vector $w$. For a positive vector $u\in(0,\infty)^n$ and a real weight vector $w$, write $\ell_w(u)=\sum_{i=1}^n w_i\log u_i$.
--
--   For every integer $k\ge0$, the following two sets of positive weight vectors are equal:
--
--   1. Those $w$ for which the full fiber $\mathcal F_A(\widehat v(w))$ has an extreme law with support of cardinality $k$.
--   2. Those $w$ for which there exist linearly independent vectors $a_1,\ldots,a_k\in A(\Theta)$ and weights $p_j>0$, $\sum_jp_j=1$, satisfying
--   $$
--   \widehat v(w)=\sum_{j=1}^k p_j a_j.
--   $$
--
--   This equality transfers support-size events for full probability-law optimizers to finite-dimensional independent representations, where measurability and determinant estimates can be studied.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MeasureExtremeSupport.lean#L49-L87

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
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.fullExtremeSupportEvent_eq_independentRepresentationEvent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (k : ℕ) :
    fullExtremeSupportEvent A vhat k = independentRepresentationEvent (range A) vhat k := by sorry
