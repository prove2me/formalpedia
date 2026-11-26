-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_approx_regularization_conditional_balanced
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:19:08.729189+00:00
-- url     : https://prove2.me/submissions/fed6d096-3609-425a-9d80-2e8184cbf19f

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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
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
import Mathlib.MeasureTheory.Measure.Prod
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
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_CompactOptimizerEvents
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
import Definitions.Def_ReweightedNPMLE_GaussianApproxJointEvents
import Definitions.Def_ReweightedNPMLE_GaussianApproxRegularization
import Definitions.Def_ReweightedNPMLE_GaussianExactRegularization
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianJointConsistency
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
import Definitions.Def_ReweightedNPMLE_GaussianJointTheorems
import Definitions.Def_ReweightedNPMLE_GaussianMainTheorem
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianPaperScales
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianSampling
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianTinyJoint
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_IncidenceJacobian
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalancedShape_scale
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalanced_likelihood_bound
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianTaylorResidual_width_scale
import Theorems.Thm_ReweightedNPMLE_gaussian_effective_dimension_full_support
import Theorems.Thm_ReweightedNPMLE_gaussian_probability_optimizer_iff_score_fiber
import Theorems.Thm_ReweightedNPMLE_isLittleO_gaussianPaperBalancedShape_rpow

-- Inline helpers preserved from ReweightedNPMLE.FittedRegularity.
section
/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE



theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)







































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityOptimizerFiber.
section
/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





















theorem probabilityMixtureValue_eq_integral {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ = ∫ θ, A θ ∂μ := by
  have hi := hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A)
    (μ := (μ : Measure Θ))
  funext i
  exact (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi

theorem probabilityMixtureValue_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ ∈ convexHull ℝ (range A) := by
  rw [probabilityMixtureValue_eq_integral A hA μ]
  exact (convex_convexHull ℝ (range A)).integral_mem
    (isCompact_convexHull_of_isCompact (isCompact_range hA)).isClosed
    (Eventually.of_forall fun θ ↦ subset_convexHull ℝ _ (mem_range_self θ))
    (hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A))













end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianStructural.
section
/-!
# Gaussian dictionary links for full-measure structural bounds

The canceled Gaussian score dictionary has the same optimizer fibers as the
Gaussian density dictionary. Its relative fitted hull is the convex hull of
the relative atoms used in the verified Taylor-width estimate.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE





theorem probabilityMixtureValue_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * probabilityMixtureValue A μ := by
  funext i
  exact integral_const_mul (c i) (fun θ ↦ A θ i)













end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianPaperScales.
section
/-!
# Eventual scales for Gaussian exact regularization

The paper's logarithmic effective dimension, balanced Gamma shape, Taylor
rank, and remainder conditions are consequences, rather than assumptions.
Only eventual statements are used: the definitions at small sample sizes
are irrelevant.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE











theorem eventually_gaussianPaperAugmentedDimension_pos (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with n hs hl
  exact add_pos_of_nonneg_of_pos (pow_nonneg hs.1 d) hl

















theorem eventually_gaussianPaperBalancedShape_le_rpow (d : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, gaussianPaperBalancedShape d n ≤ (n : ℝ) ^ s := by
  filter_upwards [(isLittleO_gaussianPaperBalancedShape_rpow d hs).bound zero_lt_one,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
    with n hb hd hl
  have hp : 0 ≤ gaussianPaperBalancedShape d n := by
    exact mul_nonneg hd.le hl
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s), one_mul] using hb

theorem eventually_gaussianPaperStructuralTail_ge_one {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ gaussianPaperStructuralTail b n := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hl
  change 1 ≤ Real.log (n : ℝ) at hl
  dsimp [gaussianPaperStructuralTail]
  nlinarith





/-- Both scale hypotheses of the Gaussian structural theorem hold at the
paper's balanced shape; no rank or remainder estimate is left as an input. -/
theorem eventually_gaussianPaperBalanced_conditions (d : ℕ) {S b : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ gaussianPaperStructuralTail b n ∧
      0 < gaussianPaperBalancedShape d n ∧
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ gaussianPaperBalancedShape d n ∧
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 40 n) *
        Real.sqrt (gaussianPaperBalancedShape d n * (n : ℝ) *
          effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  filter_upwards [eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_gaussianPaperBalancedShape_scale d (by norm_num : (0 : ℝ) < 40) hb,
    eventually_gaussianPaperBalancedShape_le_rpow d (show (0 : ℝ) < 1 by norm_num),
    eventually_gaussianTaylorResidual_width_scale d (show (0 : ℝ) ≤ 1 by norm_num)
      (show (8 : ℝ) * (1 + 4) ≤ 40 by norm_num) hS hb]
    with n hq hd hl hscale hαle hwidth
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hd hl
  exact ⟨hq, hα, hscale, hwidth _ hα.le (by simpa only [Real.rpow_one] using hαle)⟩











theorem gaussianPaperStructural_failure_bound {n : ℕ} (hn : 0 < n) (b : ℝ) :
    3 * Real.exp (-gaussianPaperStructuralTail b n) = 3 * (n : ℝ) ^ (-(b + 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0]
  congr 2
  dsimp [gaussianPaperStructuralTail]
  ring







end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianExactRegularization.
section
/-!
# Gaussian exact regularization

This module assembles the structural Gaussian result at the paper's actual
balanced concentration. Its optimizer sets consist of all probability laws,
not just finite atomic measures. Statistical risk is assembled separately.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE



theorem gaussianCanonicalFit_isMax {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (w : Fin n → ℝ) :
    IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) (gaussianCanonicalFit x θ hθ w) :=
  fittedValueSelection_isMax _ _ _ _ w

theorem weightedLogLikelihood_mul_positive {n : ℕ} (w c v : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hv : ∀ i, 0 < v i) :
    weightedLogLikelihood w (c * v) =
      weightedLogLikelihood w c + weightedLogLikelihood w v := by
  unfold weightedLogLikelihood
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, Real.log_mul (hc i).ne' (hv i).ne']
  ring











end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianApproxRegularization.
section
/-! # Conditional ordinary fit control for approximate probability laws -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

theorem gaussianProbabilityLogLikelihood_score {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (ν : ProbabilityMeasure Θ) :
    gaussianProbabilityLogLikelihood θ ((x, w), ν) =
      weightedLogLikelihood w (fun i ↦ gaussianDensity d (x i)) +
        weightedLogLikelihood w (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) ν) := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hpos : ∀ i, 0 < probabilityMixtureValue A ν i :=
    (positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)).2.2
      (probabilityMixtureValue_mem_convexHull A hA ν)
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  unfold gaussianProbabilityLogLikelihood
  rw [hkernel, probabilityMixtureValue_coordinate_scale]
  exact weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) hpos

theorem gaussianSquaredLogRatioGap_score {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (ν μ₀ : ProbabilityMeasure Θ) :
    gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) =
      ∑ i, (fittedLogRatio
        (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) μ₀)
        (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) ν) i) ^ 2 := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hpos (μ : ProbabilityMeasure Θ) : ∀ i, 0 < probabilityMixtureValue A μ i :=
    (positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)).2.2
      (probabilityMixtureValue_mem_convexHull A hA μ)
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  unfold gaussianSquaredLogRatioGap
  dsimp only
  rw [hkernel, probabilityMixtureValue_coordinate_scale, probabilityMixtureValue_coordinate_scale]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.log ((gaussianDensity d (x i) * probabilityMixtureValue A ν i) /
    (gaussianDensity d (x i) * probabilityMixtureValue A μ₀ i))) ^ 2 = _
  rw [mul_div_mul_left _ _ (gaussianDensity_pos d (x i)).ne',
    Real.log_div (hpos ν i).ne' (hpos μ₀ i).ne']
  rfl







end ReweightedNPMLE
end

/-! # Conditional ordinary fit control for approximate probability laws -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The approximate-fit part holds simultaneously for all attainable laws on
one conditional weight event, at the paper's tolerance `c₀ / log n`. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Point d,
      (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n (gaussianPaperBalancedShape d n)
          (gaussianPaperBalancedShape d n)).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ w ∈ G, w ∈ positiveVectors n ∧
          ∀ μw ∈ gaussianProbabilityOptimizerSet θ (x, w),
            ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1), ∀ ν : ProbabilityMeasure Θ,
              gaussianProbabilityLogLikelihood θ ((x, w), μw) - gaussianPaperApproxTolerance n ≤
                gaussianProbabilityLogLikelihood θ ((x, w), ν) →
              0 ≤ gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) ∧
                gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) ≤
                  gaussianPaperApproxConstant d b / Real.log n ∧
                gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) ≤
                  gaussianPaperApproxConstant d b / Real.log n := by
  filter_upwards [eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaperBalanced_likelihood_bound d (show (0 : ℝ) < 40 by norm_num) hb,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with n hc hbase hlog hn
  change 1 < Real.log (n : ℝ) at hlog
  change 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
    gaussianPaperBalancedShape d n ≤ gaussianPaperSupportConstant d 40 b / Real.log n at hbase
  intro x hx
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by dsimp [gaussianPaperSampleRadius]; positivity
  obtain ⟨G, hG, hGprob, hgood⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder 40 n) hc.1 hT hS x hx θ hθ hθbound hc.2.2.1 hc.2.2.2
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let vhat := gaussianCanonicalFit x θ hθ
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit (w : Fin n → ℝ) := gaussianCanonicalFit_isMax x θ hθ w
  have hτ0 : 0 ≤ gaussianPaperApproxTolerance n := by
    unfold gaussianPaperApproxTolerance
    positivity
  have hτlt : gaussianPaperApproxTolerance n < 1 / 3072 := by
    unfold gaussianPaperApproxTolerance
    have hl : 0 < Real.log (n : ℝ) := by linarith
    apply (div_lt_iff₀ hl).mpr
    nlinarith
  have heffbound : 10000000 *
      (((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n + gaussianPaperApproxTolerance n) ≤
      gaussianPaperApproxConstant d b / Real.log n := by
    calc
      _ = 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n + 10000000 * gaussianPaperApproxTolerance n := by ring
      _ ≤ gaussianPaperSupportConstant d 40 b / Real.log n +
        10000000 * gaussianPaperApproxTolerance n := by linarith
      _ = _ := by
        simp only [gaussianPaperApproxConstant, gaussianPaperApproxTolerance, div_eq_mul_inv]
        ring
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b]
    exact hGprob
  · intro w hw
    obtain ⟨_, hpos, _, _, _, _, _, hnearfit⟩ := hgood w hw
    refine ⟨hpos, ?_⟩
    intro μw hμw μ₀ hμ₀ ν hnear
    have hμwscore := (gaussian_probability_optimizer_iff_score_fiber x θ hθ w (vhat w)
      hpos (hfit w) μw).mp hμw
    have hμ₀score := (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 (vhat 1)
      (fun _ ↦ by norm_num) (hfit 1) μ₀).mp hμ₀
    have hμwval : probabilityMixtureValue A μw = vhat w := hμwscore
    have hμ₀val : probabilityMixtureValue A μ₀ = vhat 1 := hμ₀score
    have hnearA : weightedLogLikelihood w (vhat w) - gaussianPaperApproxTolerance n ≤
        weightedLogLikelihood w (probabilityMixtureValue A ν) := by
      rw [gaussianProbabilityLogLikelihood_score θ hθ, gaussianProbabilityLogLikelihood_score θ hθ] at hnear
      change weightedLogLikelihood w (fun i ↦ gaussianDensity d (x i)) +
        weightedLogLikelihood w (probabilityMixtureValue A μw) - _ ≤ _ at hnear
      rw [hμwval] at hnear
      linarith
    obtain ⟨h0, h1, h2⟩ := hnearfit (gaussianPaperApproxTolerance n) hτ0 hτlt
      (probabilityMixtureValue A ν) (probabilityMixtureValue_mem_convexHull A hA ν) hnearA
    have hgapEq : gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) =
        weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (probabilityMixtureValue A ν) := by
      unfold gaussianOrdinaryLikelihoodGap
      rw [gaussianProbabilityLogLikelihood_score θ hθ, gaussianProbabilityLogLikelihood_score θ hθ]
      change _ + weightedLogLikelihood 1 (probabilityMixtureValue A μ₀) - _ = _
      rw [hμ₀val]
      ring
    have hlogEq : gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) =
        ∑ i, (fittedLogRatio (vhat 1) (probabilityMixtureValue A ν) i) ^ 2 := by
      rw [gaussianSquaredLogRatioGap_score θ hθ]
      change (∑ i, (fittedLogRatio (probabilityMixtureValue A μ₀) (probabilityMixtureValue A ν) i) ^ 2) = _
      rw [hμ₀val]
    rw [hgapEq, hlogEq]
    exact ⟨h0, h1.trans heffbound, h2.trans heffbound⟩
