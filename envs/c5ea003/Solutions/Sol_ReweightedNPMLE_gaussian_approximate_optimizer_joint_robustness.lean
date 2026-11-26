-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_approximate_optimizer_joint_robustness
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:21:34.586787+00:00
-- url     : https://prove2.me/submissions/c633cf4c-a5e5-4f20-be5d-f538f087e650

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
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_measurable_uniform_nearMLE_event
import Theorems.Thm_ReweightedNPMLE_compactGaussianSampleMeasure_paper_radius_tail
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalancedShape_scale
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianTaylorResidual_width_scale
import Theorems.Thm_ReweightedNPMLE_gaussian_approx_regularization_conditional_balanced
import Theorems.Thm_ReweightedNPMLE_gaussian_optimizer_nearMLE_of_likelihood_bound
import Theorems.Thm_ReweightedNPMLE_isLittleO_gaussianPaperBalancedShape_rpow
import Theorems.Thm_ReweightedNPMLE_measurableSet_gaussianApproxFitFailure
import Theorems.Thm_ReweightedNPMLE_measureReal_prod_le_of_uniform_section_bound

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



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointTheorems.
section
/-!
# Exact regularization on one joint probability event

The experiment is the independent product of the actual iid Gaussian-mixture
sample law and the Gamma weight law. A measurable hull of the uniform near-MLE
risk exception suffices: no measurable choice of an optimizing mixing law is
assumed.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE



theorem gaussianProbabilityLogLikelihood_one {d n : ℕ} {K : Set (Point d)}
    (x : Fin n → Point d) (G : ProbabilityMeasure K) :
    gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) ((x, 1), G) =
      ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) := by
  simp [gaussianProbabilityLogLikelihood, weightedLogLikelihood, probabilityMixtureValue,
    compactGaussianMixtureDensity, gaussianMixture]





end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianApproxJointEvents.
section
/-! # Borel simultaneous approximate-fit failures

The comparison relation includes a weighted optimizer, an ordinary optimizer,
and an arbitrary attainable approximate mixing law. Closedness and compact
law projection prove joint measurability of the universal fit conclusions.
-/

open Set MeasureTheory
open scoped Topology

namespace ReweightedNPMLE









theorem gaussian_approx_fit_bounds_of_notMem_failure {Θ : Type*}
    [MeasurableSpace Θ] {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n) (τ t : ℝ)
    (hgood : p ∉ gaussianApproxFitFailure θ τ t)
    (μw μ₀ ν : ProbabilityMeasure Θ)
    (hμw : μw ∈ gaussianProbabilityOptimizerSet θ p)
    (hμ₀ : μ₀ ∈ gaussianProbabilityOptimizerSet θ (p.1, 1))
    (hnear : gaussianProbabilityLogLikelihood θ (p, μw) - τ ≤
      gaussianProbabilityLogLikelihood θ (p, ν)) :
    0 ≤ gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ∧
      gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ t ∧
      gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ t := by
  have hgraph : (p, ((μw, μ₀), ν)) ∈ gaussianApproxComparisonGraph θ τ := ⟨⟨hμw, hμ₀⟩, hnear⟩
  have hgap : gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ t :=
    le_of_not_gt (fun h ↦ hgood (Or.inl ⟨((μw, μ₀), ν), hgraph, h⟩))
  have hlog : gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ t :=
    le_of_not_gt (fun h ↦ hgood (Or.inr ⟨((μw, μ₀), ν), hgraph, h⟩))
  exact ⟨sub_nonneg.mpr (hμ₀.2 ν (mem_univ _)), hgap, hlog⟩

end ReweightedNPMLE
end

/-! # Statistical robustness to numerical optimization

This theorem controls every attainable approximate law simultaneously on one
Borel joint experiment event. It makes no sparsity claim for approximate laws.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Corollary `cor:approx`, with the fixed sufficiently small tolerance
constant `c₀ = 1/6144`. No approximate optimizer is assumed to be atomic. -/
theorem solution
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, ∀ μw ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p,
          ∀ ν : ProbabilityMeasure K,
            gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) (p, μw) -
              gaussianPaperApproxTolerance n ≤
                gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) (p, ν) →
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ≤ C / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity ν) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  have hθbound : ∀ a : K, ‖θ a‖ ≤ S := fun a ↦ hKbound a.val a.property
  let B := gaussianPaperApproxConstant d b
  let R := gaussianPaperRateConstant d b
  let F := 4 * (d : ℝ) + 5
  let C := 1 + B + R + F
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperApproxConstant, gaussianPaperSupportConstant]; positivity
  have hR : 0 ≤ R := by dsimp [R, gaussianPaperRateConstant, gaussianPaperEntropyConstant]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussian_approx_regularization_conditional_balanced d hS hb.le θ hθ hθbound,
    compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty hS hb.le hKbound,
    eventually_gaussianPaperBalanced_conditions d hS hb.le,
    eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B,
    eventually_ge_atTop (1 : ℕ)] with n hcond hrisk hscale hlogscale hlog hlogB hn
  intro Gstar
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let P := compactGaussianSampleMeasure Gstar n
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  let E : Set (GaussianDataWeight d n) := gaussianApproxFitFailure θ
    (gaussianPaperApproxTolerance n) (B / Real.log n)
  have hE : MeasurableSet E := measurableSet_gaussianApproxFitFailure θ hθ _ _
  let D : Set (Fin n → Point d) := {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hD : MeasurableSet D := by
    have heq : D = ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by
      ext x
      simp [D]
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const ((continuous_apply i).norm.measurable))
  have hDprob : P.real D ≤ (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) :=
    compactGaussianSampleMeasure_paper_radius_tail Gstar hS hb.le hKbound hlog hn
  have hsections : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx ⟨i, lt_of_not_ge h⟩
    obtain ⟨H, hH, hHprob, hgood⟩ := hcond x hxrad
    apply le_trans (measureReal_mono (μ := Q) (s₂ := Hᶜ) ?_) hHprob
    intro w hw
    by_contra hwH
    obtain ⟨hpos, hfit⟩ := hgood w (not_not.mp hwH)
    simp only [E, gaussianApproxFitFailure, mem_preimage, mem_union, mem_setOf_eq] at hw
    rcases hw with hgap | hlogfit
    · obtain ⟨⟨⟨μw, μ₀⟩, ν⟩, hg, hbad⟩ := hgap
      exact (not_lt_of_ge (hfit μw hg.1.1 μ₀ hg.1.2 ν hg.2).2.1) hbad
    · obtain ⟨⟨⟨μw, μ₀⟩, ν⟩, hg, hbad⟩ := hlogfit
      exact (not_lt_of_ge (hfit μw hg.1.1 μ₀ hg.1.2 ν hg.2).2.2) hbad
  have hEprob : (P.prod Q).real E ≤ (2 * (d : ℝ) + 4) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
      (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsections
    exact h.trans (by linarith)
  obtain ⟨N, hN, hNprob, hNgood⟩ := hrisk Gstar
  refine ⟨(E ∪ (N ×ˢ univ))ᶜ, (hE.union (hN.prod MeasurableSet.univ)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    have hNprod : (P.prod Q).real (N ×ˢ univ) = P.real N := by simp
    have h := measureReal_union_le (μ := P.prod Q) E (N ×ˢ univ)
    rw [hNprod] at h
    have htotal : (P.prod Q).real (E ∪ (N ×ˢ univ)) ≤ F * (n : ℝ) ^ (-(b + 2)) := by linarith
    have hpow : (n : ℝ) ^ (-(b + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    exact htotal.trans (mul_le_mul hFC hpow (by positivity) hC.le)
  · intro p hp μw hμw ν hnear
    have hpE : p ∉ E := fun h ↦ hp (Or.inl h)
    have hpN : p.1 ∉ N := fun h ↦ hp (Or.inr ⟨h, mem_univ _⟩)
    have hcompare : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (p.1, 1),
        0 ≤ gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ∧
          gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ B / Real.log n ∧
          gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ B / Real.log n :=
      fun μ₀ hμ₀ ↦ gaussian_approx_fit_bounds_of_notMem_failure θ p _ _ hpE μw μ₀ ν hμw hμ₀ hnear
    refine ⟨?_, ?_⟩
    · intro μ₀ hμ₀
      obtain ⟨h0, h1, h2⟩ := hcompare μ₀ hμ₀
      have hdiv := div_le_div_of_nonneg_right hBC hlog.le
      exact ⟨h0, h1.trans hdiv, h2.trans hdiv⟩
    · have ht : B / Real.log n ≤ 1 := (div_le_one hlog).mpr hlogB
      have hnearν := gaussian_optimizer_nearMLE_of_likelihood_bound θ hθ p.1 p.2 ν ht
        (fun μ₀ hμ₀ ↦ (hcompare μ₀ hμ₀).2.1) Gstar
      rw [gaussianProbabilityLogLikelihood_one, gaussianProbabilityLogLikelihood_one] at hnearν
      have hris := hNgood p.1 hpN ν hnearν
      have hris' : hellingerSq volume (compactGaussianMixtureDensity ν) (compactGaussianMixtureDensity Gstar) ≤
          R * gaussianPaperRiskScale d n := by
        simpa only [R, gaussianPaperRiskScale, mul_assoc, mul_div_assoc] using hris
      have hs : 0 ≤ gaussianPaperRiskScale d n :=
        div_nonneg (mul_nonneg (pow_nonneg hlogscale.1 d) hlog.le) (Nat.cast_nonneg _)
      exact hris'.trans (mul_le_mul_of_nonneg_right hRC hs)
