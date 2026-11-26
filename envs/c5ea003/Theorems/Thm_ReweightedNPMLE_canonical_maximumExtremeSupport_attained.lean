-- Prove2me | Theorems.Thm_ReweightedNPMLE_canonical_maximumExtremeSupport_attained
-- name    : ReweightedNPMLE.canonical_maximumExtremeSupport_attained
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:39.588627+00:00
-- url     : https://prove2.me/theorems/e55a3397-c56d-52b0-8fb6-ec6f6b705689
-- title:
--   The maximal support size of a canonical extreme optimizer is attained
-- statement:
--   Let $n\ge0$, let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $A:\Theta\to\mathbb R^n$ be continuous. For $v\in\mathbb R^n$, define its probability-mixture fiber by
--   $$
--   \mathcal F_A(v)=\left\{\mu\in\mathcal P(\Theta):\int_\Theta A(a)\,d\mu(a)=v\right\}.
--   $$
--   Extreme points refer to the full fiber of probability measures, not only to a finite dictionary of atoms.
--
--   Assume $n\ge1$. Let $C\subseteq(0,\infty)^n$ be nonempty, compact, and convex, with
--   $$
--   A(\Theta)\subseteq C\subseteq\operatorname{conv}(A(\Theta)).
--   $$
--   Let $\widehat v(w)$ be the canonical maximizer of $\ell_w$ on $C$, and fix strictly positive weights $w$. For a positive vector $u\in(0,\infty)^n$ and a real weight vector $w$, write $\ell_w(u)=\sum_{i=1}^n w_i\log u_i$.
--
--   Let $M(w)$ be the natural-number supremum of support cardinalities of extreme laws in $\mathcal F_A(\widehat v(w))$. Then
--   $$
--   1\le M(w)\le n,
--   $$
--   and some extreme law $\mu$ attains this value:
--   $$
--   \mu\in\operatorname{ext}\mathcal F_A(\widehat v(w)),\qquad
--   |\operatorname{supp}(\mu)|=M(w).
--   $$
--
--   Thus the maximum extreme-support statistic used in the structural bounds is positive, finite, and realized by an actual probability-law optimizer.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/MeasureExtremeSupport.lean#L137-L159

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

theorem ReweightedNPMLE.canonical_maximumExtremeSupport_attained {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (hChull : C ⊆ convexHull ℝ (range A))
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
      ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
        (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w := by sorry
