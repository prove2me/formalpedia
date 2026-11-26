-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_reweighted_optimizer_weak_consistency
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:23:13.707151+00:00
-- url     : https://prove2.me/submissions/b135fac9-4f3b-4ca6-9b9e-f1c81c7dc6f9

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_weak_consistency_of_hellingerSq_tails
import Theorems.Thm_ReweightedNPMLE_gaussian_exact_regularization_joint_balanced_explicit

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













































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianJointConsistency.
section
/-! # Weak consistency of the reweighted mixing law

Any optimizer rule satisfies weak consistency. Measurability of the rule is
not needed for this outer-probability formulation. At the finitely many
irrelevant small sample sizes with nonpositive balanced shape, the experiment
uses shape one so that every experiment is a genuine probability law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE





theorem tendsto_gaussianPaperRiskScale_zero (d : ℕ) :
    Tendsto (gaussianPaperRiskScale d) atTop (𝓝 0) := by
  have hpoly : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ (d + 1) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := d + 1)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hpoly
  · filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with n hs hl
    exact div_nonneg (mul_nonneg (pow_nonneg hs.1 d) hl) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with n hs hl
    unfold gaussianPaperRiskScale
    rw [pow_succ]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 d) hl) (Nat.cast_nonneg _)



end ReweightedNPMLE
end

/-! # Weak consistency of the reweighted mixing law

Any optimizer rule satisfies weak consistency. Measurability of the rule is
not needed for this outer-probability formulation. At the finitely many
irrelevant small sample sizes with nonpositive balanced shape, the experiment
uses shape one so that every experiment is a genuine probability law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Corollary `cor:weak`, for any rule selecting a weighted NPMLE at positive
weights. The sample space includes both observations and independent weights. -/
theorem solution
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S : ℝ} (hS : 0 ≤ S) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (Gstar : ProbabilityMeasure K)
    (Ghat : ∀ n : ℕ, GaussianDataWeight d n → ProbabilityMeasure K)
    (hGhat : ∀ n p, p.2 ∈ positiveVectors n →
      Ghat n p ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p) :
    ∀ U ∈ 𝓝 Gstar, Tendsto (fun n ↦ (gaussianBalancedExperimentMeasure Gstar n).real
      {p | Ghat n p ∉ U}) atTop (𝓝 0) := by
  apply gaussianMixture_weak_consistency_of_hellingerSq_tails hKcompact Gstar
    (gaussianBalancedExperimentMeasure Gstar) Ghat
  intro δ hδ
  have hrate : Tendsto (fun n ↦ gaussianPaperRateConstant d 1 * gaussianPaperRiskScale d n)
      atTop (𝓝 0) := by
    simpa using (tendsto_gaussianPaperRiskScale_zero d).const_mul (gaussianPaperRateConstant d 1)
  have htail : Tendsto (fun n : ℕ ↦ (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(1 + 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 + 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop |>.const_mul (4 * (d : ℝ) + 5)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ htail
  filter_upwards [gaussian_exact_regularization_joint_balanced_explicit hd K hKcompact hKnonempty
      hS (show (0 : ℝ) ≤ 1 by norm_num) hKbound,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    hrate.eventually (gt_mem_nhds hδ)] with n hmain hdim hlog hsmall
  obtain ⟨G, hG, hGprob, hgood⟩ := hmain Gstar
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hdim hlog
  have heq : gaussianBalancedExperimentMeasure Gstar n =
      gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n) := by
    simp [gaussianBalancedExperimentMeasure, hα]
  letI : IsProbabilityMeasure (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)) := by
    rw [← heq]
    infer_instance
  rw [heq]
  apply le_trans (measureReal_mono (s₂ := Gᶜ) ?_) hGprob
  intro p hp
  by_contra hpG
  obtain ⟨_, hpos, μ, huniq, _, _, _, hrisk⟩ := hgood p (not_not.mp hpG)
  have hμ : Ghat n p = μ := by
    have h := hGhat n p hpos
    rwa [huniq, mem_singleton_iff] at h
  simp only [mem_setOf_eq] at hp
  rw [hμ] at hp
  change δ ≤ hellingerSq volume (compactGaussianMixtureDensity μ)
    (compactGaussianMixtureDensity Gstar) at hp
  have hrisk' : hellingerSq volume (compactGaussianMixtureDensity μ)
      (compactGaussianMixtureDensity Gstar) ≤ gaussianPaperRateConstant d 1 * gaussianPaperRiskScale d n := by
    simpa only [gaussianPaperRiskScale, mul_div_assoc, mul_assoc] using hrisk
  exact (not_lt_of_ge (hp.trans hrisk')) hsmall
