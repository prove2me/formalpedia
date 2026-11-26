-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianPaperTiny_conditions
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:00.733331+00:00
-- url     : https://prove2.me/submissions/c2740ec6-cebe-4f3d-8f84-97343f5d0c74

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
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
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianPaperScales
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStructuralRank_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianTaylorResidual_width_scale
import Theorems.Thm_ReweightedNPMLE_isLittleO_gaussianPaperAugmentedDimension_rpow

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













theorem eventually_gaussianPaperStructuralTail_ge_one {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ gaussianPaperStructuralTail b n := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hl
  change 1 ≤ Real.log (n : ℝ) at hl
  dsimp [gaussianPaperStructuralTail]
  nlinarith

























end ReweightedNPMLE
end

/-!
# Eventual scales for Gaussian exact regularization

The paper's logarithmic effective dimension, balanced Gamma shape, Taylor
rank, and remainder conditions are consequences, rather than assumptions.
Only eventual statements are used: the definitions at small sample sizes
are irrelevant.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

open ReweightedNPMLE
open ReweightedNPMLE in
/-- For `alpha = n^(2L+2)`, the paper's scale conditions hold as well.
The Taylor order stays logarithmic; only its fixed constant depends on `L`. -/
theorem solution (d : ℕ) {S b L : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ gaussianPaperStructuralTail b n ∧
      10000000 * ((gaussianPaperStructuralRank d (8 * (2 * L + 6)) n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ (n : ℝ) ^ (2 * L + 2) ∧
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder (8 * (2 * L + 6)) n) *
        Real.sqrt ((n : ℝ) ^ (2 * L + 2) * (n : ℝ) *
          effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  let C := 8 * (2 * L + 6)
  let A := 1 + (4 * C + 1) ^ d + (b + 4)
  have hC : 0 < C := by dsimp [C]; linarith
  have hA : 0 ≤ 10000000 * A := by dsimp [A]; positivity
  have hsmall := (isLittleO_gaussianPaperAugmentedDimension_rpow d
    (show 0 < 2 * L + 2 by linarith)).const_mul_left (10000000 * A)
  filter_upwards [eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_gaussianPaperStructural_complexity_le d hC hb,
    hsmall.bound zero_lt_one, eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_gaussianTaylorResidual_width_scale d (show 0 ≤ 2 * L + 2 by linarith)
      (show 8 * ((2 * L + 2) + 4) ≤ C by dsimp [C]; ring_nf; exact le_rfl) hS hb]
    with n hq hc hbound hd hwidth
  have hbound' : 10000000 * A * gaussianPaperAugmentedDimension d n ≤
      (n : ℝ) ^ (2 * L + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hd.le),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), one_mul] using hbound
  refine ⟨hq, ?_, hwidth _ (Real.rpow_nonneg (Nat.cast_nonneg n) _) le_rfl⟩
  calc
    _ ≤ 10000000 * (A * gaussianPaperAugmentedDimension d n) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ (n : ℝ) ^ (2 * L + 2) := by nlinarith
