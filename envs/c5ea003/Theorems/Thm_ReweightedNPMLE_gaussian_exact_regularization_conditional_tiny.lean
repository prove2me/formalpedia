-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussian_exact_regularization_conditional_tiny
-- name    : ReweightedNPMLE.gaussian_exact_regularization_conditional_tiny
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:49:56.799111+00:00
-- url     : https://prove2.me/theorems/8f4a0165-5754-57f2-83b6-70ee518e33cb
-- title:
--   Conditional exact sparsity under arbitrarily small perturbations
-- statement:
--   Let $d,n\ge0$ be integers, let $\Theta$ be a nonempty compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous. Write $\varphi_d$ for the standard Gaussian density and, for a Borel probability measure $\mu$ on $\Theta$, put
--   $$
--   f_\mu(x)=\int_\Theta\varphi_d(x-\theta(a))\,d\mu(a),\qquad
--   \ell_w(x,\mu)=\sum_{i=1}^n w_i\log f_\mu(x_i).
--   $$
--   Here $x=(x_1,\ldots,x_n)$ is a data vector and $w\in\mathbb R^n$ is a weight vector. Let $\mathcal M_w(x)$ denote all maximizers of $\ell_w(x,\cdot)$ over probability measures on $\Theta$, and let $\mathbf1$ denote unit weights.
--
--   Assume $S,b\ge0$, $L>0$, that $\theta$ is injective, and that $\|\theta(a)\|\le S$ for every $a\in\Theta$. Put
--   $$
--   a_{d,n}=\left(\frac{\log n}{\log\log n}\right)^d+\log n,\quad
--   T_{d,S,b,n}=S+\sqrt d\sqrt{2(b+4)\log n},\quad
--   C_L=8(2L+6),\quad
--   B_{d,b,L}=10^7\bigl(1+(4C_L+1)^d+b+4\bigr).
--   $$
--   For every sufficiently large $n$, there is a Borel data set $X_n$ with Lebesgue-null complement. For each $x\in X_n$ with $\max_i\|x_i\|\le T_{d,S,b,n}$, a Borel event $G$ of independent Gamma weights with common shape and rate $n^{2L+2}$ satisfies
--   $$
--   \Pr(W\notin G)\le3n^{-(b+2)}.
--   $$
--   For every $w\in G$, all weights are positive, $\max_i|w_i-1|\le n^{-L}$, and there is a probability law $\mu$ such that
--   $$
--   \mathcal M_w(x)=\{\mu\},\qquad
--   \operatorname{supp}(\mu)\text{ finite},\qquad
--   |\operatorname{supp}(\mu)|\le B_{d,b,L}a_{d,n}.
--   $$
--   The same law is an ordinary near-MLE with total log-likelihood error at most one:
--   $$
--   \ell_{\mathbf1}(x,\nu)-1\le\ell_{\mathbf1}(x,\mu)
--   \qquad\text{for every }\nu\in\mathcal P(\Theta).
--   $$
--
--   This result permits any prescribed polynomial rate of perturbation decay while preserving exact finite sparsity and the near-MLE condition needed for uniform statistical risk bounds.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianExactRegularization.lean#L243-L363

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Implicit
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
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
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
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
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
import Definitions.Def_ReweightedNPMLE_GaussianExactRegularization
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianPaperScales
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_IncidenceJacobian
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Gaussian exact regularization

This module assembles the structural Gaussian result at the paper's actual
balanced concentration. Its optimizer sets consist of all probability laws,
not just finite atomic measures. Statistical risk is assembled separately.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussian_exact_regularization_conditional_tiny {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b L : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n ((n : ℝ) ^ (2 * L + 2))
          ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
      ∀ w ∈ G,
        (∀ i, |w i - 1| ≤ (n : ℝ) ^ (-L)) ∧ w ∈ positiveVectors n ∧
        ∃ μ : ProbabilityMeasure Θ,
          {ν : ProbabilityMeasure Θ | IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦
            weightedLogLikelihood w
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) ν} = {μ} ∧
          (μ : Measure Θ).support.Finite ∧
          ((μ : Measure Θ).support.ncard : ℝ) ≤
            gaussianPaperSupportConstant d (8 * (2 * L + 6)) b *
              gaussianPaperAugmentedDimension d n ∧
          ∀ ν : ProbabilityMeasure Θ,
            weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ν) - 1 ≤
            weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ) := by sorry
