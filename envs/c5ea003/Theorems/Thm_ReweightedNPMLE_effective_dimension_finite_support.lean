-- Prove2me | Theorems.Thm_ReweightedNPMLE_effective_dimension_finite_support
-- name    : ReweightedNPMLE.effective_dimension_finite_support
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:48:03.393479+00:00
-- url     : https://prove2.me/theorems/9e6adfb5-90dc-5bae-b2c6-2cb779ffef7f
-- title:
--   Effective-dimension sparsification for finite dictionary representations
-- statement:
--   Let $n\ge1$ and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex. Define $\ell_w(v)=\sum_iw_i\log v_i$. Let $\widehat v(w)$ denote a maximizing fitted vector, unique when $w>0$, and set $v_0=\widehat v(\mathbf1)$. Let $V$ be a Euclidean subspace with orthogonal projection $\Pi$, and assume $\operatorname{dist}(v/v_0-\mathbf1,V)\le\eta$ for all $v\in C$, where $\eta\ge0$. Let $D\subset C$ be closed and generate $C$ by convex combinations, and assume $\dim V\le r$. For $q\ge1$, set $Q=q+\log(2n)$ and assume
--   $$\alpha\ge10^7(r+Q),\qquad\eta\sqrt{\alpha nQ}\le1.$$
--   Let $k(w)$ denote the largest size of a linearly independent list in $D$ representing $\widehat v(w)$ with strictly positive convex coefficients, defaulting to zero if none exists. For iid Gamma weights of shape and rate $\alpha$, there is one measurable event with probability at least $1-3e^{-q}$ on which weights are positive, $\|w-\mathbf1\|_\infty\le2\sqrt{Q/\alpha}$, and $k(w)\le10^7(r+q)$. Both the ordinary likelihood loss and $\|\log(\widehat v(w)/v_0)\|_2^2$ are at most $10^7(r+q)/\alpha$, with nonnegative likelihood loss. Simultaneously, every attainable $\tau$-optimal fit, $0\le\tau<1/3072$, has nonnegative ordinary loss, and both corresponding errors are at most $10^7((r+q)/\alpha+\tau)$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/EffectiveSparsification.lean#L260-L312

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
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Real
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
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.effective_dimension_finite_support
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (hChull : C ⊆ convexHull ℝ D)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumIndependentSupport D vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
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
