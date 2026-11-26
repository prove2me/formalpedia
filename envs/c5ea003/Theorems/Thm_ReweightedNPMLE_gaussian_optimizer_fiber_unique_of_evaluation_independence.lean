-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussian_optimizer_fiber_unique_of_evaluation_independence
-- name    : ReweightedNPMLE.gaussian_optimizer_fiber_unique_of_evaluation_independence
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:49:26.171242+00:00
-- url     : https://prove2.me/theorems/fe3d0305-8268-5f52-b5da-9654b5aecda6
-- title:
--   Gaussian evaluation independence makes a small extreme-support fiber unique
-- statement:
--   Let $d,m\ge0$ and $n\ge1$ be integers. Let $\Theta$ be a compact metric space with its Borel $\sigma$-algebra, and let $\theta:\Theta\to\mathbb R^d$ be continuous and injective. Fix data $x_1,\ldots,x_n\in\mathbb R^d$ and strictly positive weights $w_i$. Define
--   $$
--   A(a)_i=e^{\langle x_i,\theta(a)\rangle-\|\theta(a)\|^2/2},\quad
--   K(a)_i=\varphi_d(x_i-\theta(a)),\quad c_i=\varphi_d(x_i).
--   $$
--   Suppose $v$ maximizes $\sum_iw_i\log u_i$ over $u\in\operatorname{conv}(A(\Theta))$, and assume $(2m)(d+1)\le n$.
--
--   Assume simultaneous evaluation independence: whenever $k(d+1)\le n$ and $t_1,\ldots,t_k\in\mathbb R^d$ are distinct, the vectors $(\varphi_d(x_i-t_j))_{i=1}^n$, $j=1,\ldots,k$, are linearly independent. Also assume every extreme law in $\mathcal F_A(v)=\{\rho:\int A\,d\rho=v\}$ has support cardinality at most $m$.
--
--   Then some probability law $\mu$ satisfies
--   $$
--   \mathcal F_K(c\odot v)=\{\mu\},\qquad
--   \mu\in\operatorname{ext}\mathcal F_K(c\odot v),\qquad
--   \operatorname{supp}(\mu)\text{ finite},\qquad |\operatorname{supp}(\mu)|\le m,
--   $$
--   where $\mathcal F_K(y)=\{\rho:\int K\,d\rho=y\}$ and $c\odot v$ is coordinatewise multiplication.
--
--   The independence hypothesis covers arbitrary, including data-dependent, locations. This lemma converts generic evaluation geometry and an extreme-support bound into uniqueness over the full space of mixing laws.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianStructural.lean#L189-L249

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

theorem ReweightedNPMLE.gaussian_optimizer_fiber_unique_of_evaluation_independence {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n m : ℕ} [Nonempty (Fin n)] (x : Fin n → Point d)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) v)
    (hsize : (2 * m) * (d + 1) ≤ n)
    (hgeneric : ∀ k : ℕ, k * (d + 1) ≤ n → ∀ t : Fin k → Point d,
      Function.Injective t → LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (t j)))
    (hsmall : ∀ μ : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture (fun a ↦ gaussianScoreFeature x (θ a)) v μ →
        (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ,
      probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) = {μ} ∧
      IsExtremeProbabilityMixture (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) μ ∧
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by sorry
