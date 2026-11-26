-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussian_effective_dimension_full_support
-- name    : ReweightedNPMLE.gaussian_effective_dimension_full_support
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:48:51.871085+00:00
-- url     : https://prove2.me/theorems/0576c00e-d345-55cc-98b7-3b1be6fdcb8f
-- title:
--   Finite-sample Gaussian support and fit bounds from Taylor effective dimension
-- statement:
--   Let $d,L\ge0$ and $n\ge1$ be integers. Let $\Theta$ be a nonempty compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous. Fix $T,S\ge0$, data $x_1,\ldots,x_n$ with $\|x_i\|\le T$, and parameter locations satisfying $\|\theta(a)\|\le S$. Define
--   $$
--   A(a)_i=\exp\!\left(\langle x_i,\theta(a)\rangle-\tfrac12\|\theta(a)\|^2\right),\quad
--   C=\operatorname{conv}(A(\Theta)),\quad
--   \ell_w(v)=\sum_{i=1}^n w_i\log v_i.
--   $$
--   Let $\widehat v(w)$ be the canonical maximizer of $\ell_w$ on $C$, and write $v_0=\widehat v(\mathbf1)$. For real $q\ge1$ and $\alpha$, put
--   $$
--   r=1+\binom{L+d}{d},\qquad Q=q+\log(2n),\qquad
--   \eta=\sqrt n\,e^{2TS+S^2/2}\frac{(TS)^{L+1}}{(L+1)!}.
--   $$
--   Assume
--   $$
--   10^7(r+Q)\le\alpha,\qquad \eta\sqrt{\alpha nQ}\le1.
--   $$
--   Then there is a Borel event $G$ for independent Gamma weights with common shape and rate $\alpha$ such that $\Pr(W\notin G)\le3e^{-q}$. Every $w\in G$ has positive coordinates and
--   $$
--   \max_i|w_i-1|\le2\sqrt{Q/\alpha}.
--   $$
--   Every extreme law in the full probability fiber $\{\mu:\int A\,d\mu=\widehat v(w)\}$ has finite support of size at most $10^7(r+q)$, and the maximum extreme-support statistic obeys the same bound. Moreover,
--   $$
--   0\le\ell_{\mathbf1}(v_0)-\ell_{\mathbf1}(\widehat v(w))\le\frac{10^7(r+q)}{\alpha},\qquad
--   \sum_i\bigl(\log\widehat v(w)_i-\log(v_0)_i\bigr)^2\le\frac{10^7(r+q)}{\alpha}.
--   $$
--   On the same event, for every $0\le\tau<1/3072$ and every $v\in C$ with $\ell_w(v)\ge\ell_w(\widehat v(w))-\tau$,
--   $$
--   0\le\ell_{\mathbf1}(v_0)-\ell_{\mathbf1}(v)\le10^7\left(\frac{r+q}{\alpha}+\tau\right),\qquad
--   \sum_i\bigl(\log v_i-\log(v_0)_i\bigr)^2\le10^7\left(\frac{r+q}{\alpha}+\tau\right).
--   $$
--
--   This is a finite-sample conditional result for fixed data. It requires no sampling distribution or model-correctness assumption; the later paper-scale theorems only specialize the rank, remainder, and Gamma-shape conditions.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianStructural.lean#L107-L187

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
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
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
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedGeometry
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_FullEffectiveDimension
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Gaussian dictionary links for full-measure structural bounds

The canceled Gaussian score dictionary has the same optimizer fibers as the
Gaussian density dictionary. Its relative fitted hull is the convex hull of
the relative atoms used in the verified Taylor-width estimate.
-/

open Set MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussian_effective_dimension_full_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (L : ℕ) {α q T S : ℝ}
    (hq : 1 ≤ q) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (x : Fin n → Point d) (hx : ∀ i, ‖x i‖ ≤ T)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S)
    (hscale : 10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : gaussianTaylorResidual n T S L *
      Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1) :
    let A := fun a : Θ ↦ gaussianScoreFeature x (θ a)
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.2
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumExtremeSupport A vhat w : ℝ) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) ∧
        (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
          (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤
            10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q)) ∧
        0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
        weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        ∀ τ : ℝ, 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) ∧
          (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) := by sorry
