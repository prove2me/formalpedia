-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianTaylorResidual_width_scale
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:13:52.166269+00:00
-- url     : https://prove2.me/submissions/741e08d6-8e3e-456e-be9c-fde5ef6268f0

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
import Theorems.Thm_ReweightedNPMLE_eventually_effectiveQ_gaussianPaperStructuralTail_le_nat
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentRelativeError_paper_le
import Theorems.Thm_ReweightedNPMLE_gaussianTaylorResidual_le_momentRelativeError

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



























theorem eventually_gaussianTaylorResidual_paper_le (d : ℕ) {C S b : ℝ}
    (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) ≤
        Real.sqrt n * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
  filter_upwards [eventually_gaussianMomentRelativeError_paper_le d hC hS hb,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
    with n he hl
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by
    dsimp [gaussianPaperSampleRadius, gaussianPaperRadiusExponent]
    positivity
  exact (gaussianTaylorResidual_le_momentRelativeError hT hS n _).trans
    (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _))



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
/-- A polynomial upper bound on the Gamma shape suffices for the width
condition, after increasing only the constant in the logarithmic Taylor order.
This includes both the balanced and every arbitrarily tiny regime. -/
theorem solution (d : ℕ) {a C S b : ℝ}
    (ha : 0 ≤ a) (hC : 8 * (a + 4) ≤ C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ α : ℝ, 0 ≤ α → α ≤ (n : ℝ) ^ a →
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) *
        Real.sqrt (α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  have hCpos : 0 < C := by linarith
  filter_upwards [eventually_gaussianTaylorResidual_paper_le d hCpos hS hb,
    eventually_effectiveQ_gaussianPaperStructuralTail_le_nat hb,
    eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_ge_atTop (1 : ℕ)] with n he hQ hq hn
  intro α hα hαbound
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2n : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hQ0 : 0 ≤ effectiveQ n (gaussianPaperStructuralTail b n) := by
    dsimp [effectiveQ]
    linarith
  have hinside : α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n) ≤
      (n : ℝ) ^ (a + 2) := by
    calc
      _ ≤ (n : ℝ) ^ a * (n : ℝ) * (n : ℝ) := by gcongr
      _ = (n : ℝ) ^ (a + 2) := by
        rw [show (n : ℝ) ^ a * (n : ℝ) * (n : ℝ) =
          (n : ℝ) ^ a * (n : ℝ) ^ (2 : ℝ) by norm_num [pow_two]; ring,
          ← Real.rpow_add hn0]
  have hsqrt : Real.sqrt (α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n)) ≤
      (n : ℝ) ^ ((a + 2) / 2) := by
    calc
      _ ≤ Real.sqrt ((n : ℝ) ^ (a + 2)) := Real.sqrt_le_sqrt hinside
      _ = (n : ℝ) ^ ((a + 2) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  calc
    _ ≤ (Real.sqrt n * (n : ℝ) ^ (1 - C / 8 : ℝ)) *
        (n : ℝ) ^ ((a + 2) / 2) :=
      mul_le_mul he hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = (n : ℝ) ^ ((1 / 2 : ℝ) + (1 - C / 8) + (a + 2) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
