-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_balanced_joint_structural_bound
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:20:19.125998+00:00
-- url     : https://prove2.me/submissions/963f21a1-6c6e-48e4-bf1b-29500d6973e9

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
import Definitions.Def_ReweightedNPMLE_GaussianExactRegularization
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianJointEvents
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
import Definitions.Def_ReweightedNPMLE_SmallSupportProbability
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperBalancedShape_scale
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianTaylorResidual_width_scale
import Theorems.Thm_ReweightedNPMLE_gaussian_exact_regularization_conditional_balanced
import Theorems.Thm_ReweightedNPMLE_isLittleO_gaussianPaperBalancedShape_rpow
import Theorems.Thm_ReweightedNPMLE_measurableSet_gaussianStructuralFailure
import Theorems.Thm_ReweightedNPMLE_measureReal_prod_le_of_uniform_section_bound
import Theorems.Thm_ReweightedNPMLE_notMem_gaussianStructuralFailure_of_unique_optimizer

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

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointStructural.
section
/-!
# Joint data-and-weight structural probability

The conditional structural conclusion controls sections of one Borel joint
failure event. This makes the integrated theorem independent of any choice
of conditional good sets.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

theorem gaussian_balanced_structural_sections {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      (gammaProductMeasure n (gaussianPaperBalancedShape d n)
        (gaussianPaperBalancedShape d n)).real
        (Prod.mk x ⁻¹' gaussianStructuralFailure θ
          (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
          (gaussianPaperSupportConstant d 40 b / Real.log n)
          ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))) ≤
        3 * (n : ℝ) ^ (-(b + 2)) := by
  filter_upwards [gaussian_exact_regularization_conditional_balanced d hS hb θ hθ hθinj hθbound,
    eventually_gaussianPaperBalanced_conditions d hS hb] with n hcond hscale
  obtain ⟨X, hX, hnull, hcond⟩ := hcond
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx hrad
  obtain ⟨G, hG, hGprob, hgood⟩ := hcond x hx hrad
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) :=
      isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  apply le_trans (measureReal_mono (μ := Q) (s₂ := Gᶜ) ?_) hGprob
  intro w hw
  by_contra hwG
  have hwG' : w ∈ G := not_not.mp hwG
  obtain ⟨hcoord, hwpos, μ, hunique, hfinite, hcard, hcompare⟩ := hgood w hwG'
  exact notMem_gaussianStructuralFailure_of_unique_optimizer θ x w _ _ _ hcoord hwpos
    μ hunique hfinite hcard (fun μ₀ hμ₀ ↦ ⟨(hcompare μ₀ hμ₀).2.1, (hcompare μ₀ hμ₀).2.2⟩) hw







end ReweightedNPMLE
end

/-!
# Joint data-and-weight structural probability

The conditional structural conclusion controls sections of one Borel joint
failure event. This makes the integrated theorem independent of any choice
of conditional good sets.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Integrating a Gaussian balanced structural event under any absolutely
continuous data law. Only its sample-radius failure remains on the right. -/
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Measure (Fin n → Point d), IsProbabilityMeasure P → P ≪ volume →
      (P.prod (gammaProductMeasure n (gaussianPaperBalancedShape d n)
        (gaussianPaperBalancedShape d n))).real
        (gaussianStructuralFailure θ
          (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
          (gaussianPaperSupportConstant d 40 b / Real.log n)
          ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))) ≤
      P.real {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} +
        3 * (n : ℝ) ^ (-(b + 2)) := by
  filter_upwards [gaussian_balanced_structural_sections d hS hb θ hθ hθinj hθbound,
    eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaperAugmentedDimension_pos d] with n hsections hscale hd
  intro P hP hPac
  letI : IsProbabilityMeasure P := hP
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) :=
      isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  obtain ⟨X, hX, hnull, hsections⟩ := hsections
  let D := Xᶜ ∪ {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hrad : MeasurableSet {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    have heq : {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} =
        ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const
      ((continuous_apply i).norm.measurable))
  have hD : MeasurableSet D := hX.compl.union hrad
  have hXzero : P.real Xᶜ = 0 := by simp only [measureReal_def, hPac hnull, ENNReal.toReal_zero]
  have hDprob : P.real D ≤
      P.real {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    exact (measureReal_union_le _ _).trans (by rw [hXzero, zero_add])
  have hR : 0 ≤ gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n := by
    unfold gaussianPaperSupportConstant
    positivity
  let E : Set (GaussianDataWeight d n) := gaussianStructuralFailure θ
    (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
    (gaussianPaperSupportConstant d 40 b / Real.log n)
    ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))
  have hE : MeasurableSet E := measurableSet_gaussianStructuralFailure θ hθ hR _ _
  have hsec : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxX : x ∈ X := by
      by_contra hn
      exact hx (Or.inl hn)
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx (Or.inr ⟨i, lt_of_not_ge h⟩)
    exact hsections x hxX hxrad
  have hbound := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
    (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsec
  exact hbound.trans (by linarith)
