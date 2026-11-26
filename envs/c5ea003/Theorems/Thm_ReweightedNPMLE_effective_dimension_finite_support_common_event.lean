-- Prove2me | Theorems.Thm_ReweightedNPMLE_effective_dimension_finite_support_common_event
-- name    : ReweightedNPMLE.effective_dimension_finite_support_common_event
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:33.259547+00:00
-- url     : https://prove2.me/theorems/76f2f297-d892-5655-98f7-0090167e7926
-- title:
--   A common event for independent support control and all approximate fits
-- statement:
--   Let $n\ge1$ and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex. Define $\ell_w(v)=\sum_iw_i\log v_i$. Let $\widehat v(w)$ denote a maximizing fitted vector, unique when $w>0$, and set $v_0=\widehat v(\mathbf1)$. Let $V$ be a Euclidean subspace with orthogonal projection $\Pi$, and assume $\operatorname{dist}(v/v_0-\mathbf1,V)\le\eta$ for all $v\in C$, where $\eta\ge0$. Let $D\subset C$ be closed with $C\subset\operatorname{conv}D$, and suppose $\dim V\le r$. Put $Q=q+\log(2n)$ and $N=r\log5+q$, with $q\ge1$. Assume $\alpha>0$, $\eta\sqrt{\alpha nQ}\le1$, and $\alpha\ge\max\{1024Q,2359296N,12288\}$. Let $k(w)$ be the largest number of linearly independent points of $D$ representing $\widehat v(w)$ by a strictly positive convex combination, with zero as the default if none exists. Under iid Gamma weights with shape and rate $\alpha$, there is a measurable $G$ with $\mathbb P(G^c)\le3e^{-q}$. On $G$, weights are positive,
--   $$\|w-\mathbf1\|_\infty\le2\sqrt{Q/\alpha},\quad
--   \sqrt\alpha\|\Pi(w-\mathbf1)\|_2\le4\sqrt N,$$
--   and $k(w)>0$ with
--   $$\log(17/9)(k(w)-1)<1744N+74+q.$$
--   Simultaneously, every $\tau$-optimal $v\in C$, $0\le\tau<1/3072$, has $t=\log(v/v_0)$ and $\Delta=\ell_{\mathbf1}(v_0)-\ell_{\mathbf1}(v)$ satisfying $\|t\|_\infty\le1/8$, $\Delta\ge0$, $\alpha\Delta\le592N+26+13\alpha\tau$, and $\alpha\|t\|_2^2\le1152N+48+24\alpha\tau$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/EffectiveSparsification.lean#L63-L182

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

theorem ReweightedNPMLE.effective_dimension_finite_support_common_event
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hα : 0 < α) (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
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
    let k := maximumIndependentSupport D vhat
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, w ∈ gammaEffectiveEvent V r α q ∧ w ∈ positiveVectors n ∧ 0 < k w ∧
        Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ) < 1744 * effectiveN r q + 74 + q ∧
        ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          α * (weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v) ≤
            592 * effectiveN r q + 26 + 13 * α * τ ∧
          α * (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            1152 * effectiveN r q + 48 + 24 * α * τ := by sorry
