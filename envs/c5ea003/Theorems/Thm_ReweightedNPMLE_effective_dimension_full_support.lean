-- Prove2me | Theorems.Thm_ReweightedNPMLE_effective_dimension_full_support
-- name    : ReweightedNPMLE.effective_dimension_full_support
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:29.754448+00:00
-- url     : https://prove2.me/theorems/818fdabe-cb2f-4c9e-b61b-49fe89c326ec
-- title:
--   Theorem 3.1 — Effective-dimension exact sparsification
-- statement:
--   Let $\Theta$ be a nonempty compact metric space with its Borel sigma-algebra, let $n\ge1$, and let $A:\Theta\to(0,\infty)^n$ be continuous. Set $\mathcal C=\operatorname{conv}(A(\Theta))$, let $\widehat v(w)$ maximize $\sum_iw_i\log v_i$ on $\mathcal C$, and put $v_0=\widehat v(\mathbf1)$. Let $V\subset\mathbb R^n$ have dimension at most $r$, and suppose every $u=v/v_0-\mathbf1$, $v\in\mathcal C$, is within Euclidean distance $\eta\ge0$ of $V$. Fix $q\ge1$, $Q=q+\log(2n)$, $C_0=10^7$, and assume $\alpha\ge C_0(r+Q)$ and $\eta\sqrt{\alpha nQ}\le1$. For independent $W_i\sim\operatorname{Gamma}(\alpha,\text{rate }\alpha)$, the maximum support size $s_{\rm ext}(w)$ over extreme probability-measure optimizers is measurable. There is a measurable event of probability at least $1-3e^{-q}$ on which $W_i>0$, $\max_i|W_i-1|\le2\sqrt{Q/\alpha}$, and $1\le s_{\rm ext}(W)\le n$ with the maximum attained and $s_{\rm ext}(W)\le C_0(r+q)$. Every extreme optimizer has finite support and satisfies that bound. On the same event, the ordinary total likelihood loss and $\|\log(\widehat v(W)/v_0)\|_2^2$ are at most $C_0(r+q)/\alpha$, with nonnegative ordinary loss. Simultaneously, every $0\le\tau<1/3072$ and every attainable $v\in\mathcal C$ with weighted likelihood gap at most $\tau$ satisfy the corresponding two bounds $C_0((r+q)/\alpha+\tau)$. No support bound is asserted for arbitrary approximate laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FullEffectiveDimension.lean#L31-L103

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_FullEffectiveDimension
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Effective-dimension sparsification for the full optimizer fiber

This is the abstract paper theorem for a continuous positive dictionary on a
nonempty compact metric space. Its support statistic ranges over all extreme
probability-measure optimizers. All near-optimal-fit conclusions hold on the
same measurable event, with explicit universal constants.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.effective_dimension_full_support
    {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (hApos : ∀ θ i, 0 < A θ i)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet (convexHull ℝ (range A))
      (fittedValueSelection (convexHull ℝ (range A))
        (positive_kernel_hull_properties A hA hApos).1
        (positive_kernel_hull_properties A hA hApos).2.1
        (positive_kernel_hull_properties A hA hApos).2.2 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C (positive_kernel_hull_properties A hA hApos).1
      (positive_kernel_hull_properties A hA hApos).2.1
      (positive_kernel_hull_properties A hA hApos).2.2
    let v₀ := vhat 1
    Measurable (maximumExtremeSupport A vhat) ∧
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
        ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
          w ∈ positiveVectors n ∧
          (maximumExtremeSupport A vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
          (0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
            ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
              (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w) ∧
          (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
            (μ : Measure Θ).support.Finite ∧
              ((μ : Measure Θ).support.ncard : ℝ) ≤ 10000000 * ((r : ℝ) + q)) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
            10000000 * ((r : ℝ) + q) / α ∧
          (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ 10000000 * ((r : ℝ) + q) / α ∧
          ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
            weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
            0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
            weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
              10000000 * (((r : ℝ) + q) / α + τ) ∧
            (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
              10000000 * (((r : ℝ) + q) / α + τ) := by sorry
