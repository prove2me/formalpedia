-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_exact_regularization_conditional_balanced
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:19:10.716853+00:00
-- url     : https://prove2.me/submissions/5fb6f220-b11e-4cda-b1a8-db16700c1d21

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalancedShape_scale
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalanced_likelihood_bound
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalanced_weight_bound
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStructuralRank_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaper_sparse_uniqueness_threshold
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianTaylorResidual_width_scale
import Theorems.Thm_ReweightedNPMLE_gaussian_effective_dimension_full_support
import Theorems.Thm_ReweightedNPMLE_gaussian_generic_evaluation_independence
import Theorems.Thm_ReweightedNPMLE_gaussian_optimizer_fiber_unique_of_evaluation_independence
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

theorem probabilityMixtureFiber_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) :
    probabilityMixtureFiber (fun θ i ↦ c i * A θ i) (c * v) = probabilityMixtureFiber A v := by
  ext μ
  change probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * v ↔
    probabilityMixtureValue A μ = v
  rw [probabilityMixtureValue_coordinate_scale]
  constructor
  · intro h
    funext i
    exact mul_left_cancel₀ (hc i) (congrFun h i)
  · intro h
    rw [h]

theorem isExtremeProbabilityMixture_coordinate_scale {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture (fun θ i ↦ c i * A θ i) (c * v) μ ↔
      IsExtremeProbabilityMixture A v μ := by
  unfold IsExtremeProbabilityMixture probabilityFiberImage
  rw [probabilityMixtureFiber_coordinate_scale A c v hc]

theorem gaussian_probability_optimizer_fiber_eq_score {Θ : Type*}
    [MeasurableSpace Θ] {d n : ℕ} (x : Fin n → Point d)
    (θ : Θ → Point d) (v : Fin n → ℝ) :
    probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
      ((fun i ↦ gaussianDensity d (x i)) * v) =
        probabilityMixtureFiber (fun a ↦ gaussianScoreFeature x (θ a)) v := by
  have heq : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * gaussianScoreFeature x (θ a) i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  rw [heq]
  exact probabilityMixtureFiber_coordinate_scale _ _ _
    (fun i ↦ (gaussianDensity_pos d (x i)).ne')







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



theorem eventually_effectiveQ_gaussianPaperStructuralTail_le {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      effectiveQ n (gaussianPaperStructuralTail b n) ≤ (b + 4) * Real.log n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (Real.log 2)] with n hn hl
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change Real.log 2 ≤ Real.log (n : ℝ) at hl
  dsimp [effectiveQ, gaussianPaperStructuralTail]
  rw [Real.log_mul (by norm_num) hn0]
  nlinarith

theorem eventually_gaussianPaperStructural_complexity_le (d : ℕ)
    {C b : ℝ} (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianPaperStructuralRank d C n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n) ≤
          (1 + (4 * C + 1) ^ d + (b + 4)) * gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperStructuralRank_le d hC,
    eventually_effectiveQ_gaussianPaperStructuralTail_le hb,
    eventually_gaussianPaperLogScale_nonneg_le_log] with n hr hQ hs
  have hp : 0 ≤ gaussianPaperEffectiveDimension d n := pow_nonneg hs.1 d
  have hlog : Real.log n ≤ gaussianPaperAugmentedDimension d n := by
    dsimp [gaussianPaperAugmentedDimension]
    linarith
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ b + 4))
  nlinarith











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





theorem eventually_gaussianPaper_rank_tail_le (d : ℕ) {C b : ℝ}
    (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianPaperStructuralRank d C n : ℝ) + gaussianPaperStructuralTail b n ≤
        (1 + (4 * C + 1) ^ d + (b + 4)) * gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperStructural_complexity_le d hC hb,
    eventually_ge_atTop (1 : ℕ)] with n hc hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  dsimp [effectiveQ] at hc
  linarith





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

theorem fittedLogRatio_mul_positive {n : ℕ} (c v₀ v : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hv₀ : ∀ i, 0 < v₀ i) (hv : ∀ i, 0 < v i) :
    fittedLogRatio (c * v₀) (c * v) = fittedLogRatio v₀ v := by
  funext i
  simp only [fittedLogRatio, Pi.mul_apply, Real.log_mul (hc i).ne' (hv i).ne',
    Real.log_mul (hc i).ne' (hv₀ i).ne']
  ring









end ReweightedNPMLE
end

/-!
# Gaussian exact regularization

This module assembles the structural Gaussian result at the paper's actual
balanced concentration. Its optimizer sets consist of all probability laws,
not just finite atomic measures. Statistical risk is assembled separately.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Conditional structural parts of the main theorem at
`alpha = (r_n + log n) log n`. There is one Borel conull data set; on the
radius event the weight event has polynomial failure. Every optimizer is
the unique finite law, and the bounds hold against every ordinary NPMLE. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n (gaussianPaperBalancedShape d n)
          (gaussianPaperBalancedShape d n)).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
      ∀ w ∈ G,
        (∀ i, |w i - 1| ≤ (2 * Real.sqrt (b + 4)) /
          Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
        w ∈ positiveVectors n ∧
        ∃ μ : ProbabilityMeasure Θ,
          {ν : ProbabilityMeasure Θ | IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦
            weightedLogLikelihood w
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) ν} = {μ} ∧
          (μ : Measure Θ).support.Finite ∧
          ((μ : Measure Θ).support.ncard : ℝ) ≤
            gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n ∧
          ∀ μ₀ : ProbabilityMeasure Θ,
            IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦ weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) μ₀ →
            let f₀ := probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ₀
            let f := probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ
            0 ≤ weightedLogLikelihood 1 f₀ - weightedLogLikelihood 1 f ∧
            weightedLogLikelihood 1 f₀ - weightedLogLikelihood 1 f ≤
              gaussianPaperSupportConstant d 40 b / Real.log n ∧
            (∑ i, (Real.log (f i / f₀ i)) ^ 2) ≤
              gaussianPaperSupportConstant d 40 b / Real.log n := by
  let B := gaussianPaperSupportConstant d 40 b
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperSupportConstant]; positivity
  filter_upwards [eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaper_sparse_uniqueness_threshold d hB,
    eventually_gaussianPaper_rank_tail_le d (show (0 : ℝ) < 40 by norm_num) hb,
    eventually_gaussianPaperBalanced_likelihood_bound d (show (0 : ℝ) < 40 by norm_num) hb,
    eventually_gaussianPaperBalanced_weight_bound d hb,
    eventually_ge_atTop (1 : ℕ)] with n hc hsize hrank hlossbound hweight hn
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨X, hX, hnull, hgeneric⟩ := gaussian_generic_evaluation_independence n d
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx hxradius
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by
    dsimp [gaussianPaperSampleRadius]
    positivity
  obtain ⟨G, hG, hGprob, hgood⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder 40 n) hc.1 hT hS x hxradius θ hθ hθbound hc.2.2.1 hc.2.2.2
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let K := fun a i ↦ gaussianKernel d (x i) (θ a)
  let c := fun i ↦ gaussianDensity d (x i)
  let vhat := gaussianCanonicalFit x θ hθ
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hprops := positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)
  have hfit (w : Fin n → ℝ) : IsMaxOn (convexHull ℝ (range A))
      (weightedLogLikelihood w) (vhat w) := gaussianCanonicalFit_isMax x θ hθ w
  have hfitpos (w : Fin n → ℝ) : ∀ i, 0 < vhat w i := hprops.2.2 (hfit w).1
  have hsmallreal : 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
      gaussianPaperStructuralTail b n) ≤ B * gaussianPaperAugmentedDimension d n := by
    calc
      _ ≤ 10000000 * ((1 + (4 * 40 + 1) ^ d + (b + 4)) *
          gaussianPaperAugmentedDimension d n) := mul_le_mul_of_nonneg_left hrank (by norm_num)
      _ = _ := by dsimp [B, gaussianPaperSupportConstant]; ring
  have heqK : K = (fun a i ↦ c i * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b]
    exact hGprob
  · intro w hw
    obtain ⟨hcoord, hwpos, _, hall, hnonneg, hloss, hlog, _⟩ := hgood w hw
    change 0 ≤ weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) at hnonneg
    change weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) ≤
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n at hloss
    change (∑ i, (fittedLogRatio (vhat 1) (vhat w) i) ^ 2) ≤
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n at hlog
    change 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
      gaussianPaperBalancedShape d n ≤ B / Real.log n at hlossbound
    refine ⟨fun i ↦ (hcoord i).trans hweight, hwpos, ?_⟩
    have hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
        (μ : Measure Θ).support.ncard ≤ Nat.ceil (B * gaussianPaperAugmentedDimension d n) := by
      intro μ hμ
      have hh := ((hall μ hμ).2.trans hsmallreal).trans (Nat.le_ceil _)
      exact_mod_cast hh
    obtain ⟨μ, hfiber, hext, hfinite, _⟩ :=
      gaussian_optimizer_fiber_unique_of_evaluation_independence x θ hθ hθinj w (vhat w)
        hwpos (hfit w) hsize (hgeneric x hx) hsmall
    have hfiberscore : probabilityMixtureFiber A (vhat w) = {μ} := by
      rw [← gaussian_probability_optimizer_fiber_eq_score x θ (vhat w)]
      exact hfiber
    have hμscore : μ ∈ probabilityMixtureFiber A (vhat w) := by
      rw [hfiberscore]
      exact mem_singleton μ
    have hμext : IsExtremeProbabilityMixture A (vhat w) μ := by
      have hext' : IsExtremeProbabilityMixture K (c * vhat w) μ := hext
      rw [heqK] at hext'
      exact (isExtremeProbabilityMixture_coordinate_scale A c (vhat w)
        (fun i ↦ (gaussianDensity_pos d (x i)).ne') μ).mp hext'
    refine ⟨μ, ?_, hfinite, (hall μ hμext).2.trans hsmallreal, ?_⟩
    · ext ν
      exact (gaussian_probability_optimizer_iff_score_fiber x θ hθ w (vhat w)
        hwpos (hfit w) ν).trans (by rw [hfiberscore])
    · intro μ₀ hμ₀
      have hμ₀score := (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 (vhat 1)
        (fun _ ↦ by norm_num) (hfit 1) μ₀).mp hμ₀
      have hf : probabilityMixtureValue K μ = c * vhat w := by
        rw [heqK, probabilityMixtureValue_coordinate_scale, show probabilityMixtureValue A μ =
          vhat w from hμscore]
      have hf₀ : probabilityMixtureValue K μ₀ = c * vhat 1 := by
        rw [heqK, probabilityMixtureValue_coordinate_scale, show probabilityMixtureValue A μ₀ =
          vhat 1 from hμ₀score]
      dsimp only
      change 0 ≤ weightedLogLikelihood 1 (probabilityMixtureValue K μ₀) -
        weightedLogLikelihood 1 (probabilityMixtureValue K μ) ∧ _
      rw [hf₀, hf,
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos 1),
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos w)]
      have hlogeq : (fun i ↦ Real.log ((c * vhat w) i / (c * vhat 1) i)) =
          fittedLogRatio (vhat 1) (vhat w) := by
        funext i
        change Real.log (gaussianDensity d (x i) * vhat w i /
          (gaussianDensity d (x i) * vhat 1 i)) = fittedLogRatio (vhat 1) (vhat w) i
        rw [Real.log_div (mul_pos (gaussianDensity_pos d (x i)) (hfitpos w i)).ne'
          (mul_pos (gaussianDensity_pos d (x i)) (hfitpos 1 i)).ne']
        exact congrFun (fittedLogRatio_mul_positive c (vhat 1) (vhat w)
          (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos 1) (hfitpos w)) i
      have hsum : (∑ i, (Real.log ((c * vhat w) i / (c * vhat 1) i)) ^ 2) =
          ∑ i, (fittedLogRatio (vhat 1) (vhat w) i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [congrFun hlogeq i]
      refine ⟨by linarith, by linarith [hloss.trans hlossbound], ?_⟩
      rw [hsum]
      exact hlog.trans hlossbound
