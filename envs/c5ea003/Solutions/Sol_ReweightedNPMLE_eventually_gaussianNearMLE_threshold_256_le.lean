-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianNearMLE_threshold_256_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:11:24.865928+00:00
-- url     : https://prove2.me/submissions/a59f4491-5c00-4f5e-9055-69a892a37fb1

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianNetHellingerSqError_256_le
import Theorems.Thm_ReweightedNPMLE_eventually_log_gaussianNetCardBound_paper_le
import Theorems.Thm_ReweightedNPMLE_tendsto_id_div_log_atTop

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLERate.
section
/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

namespace ReweightedNPMLE











/-- The logarithmic Taylor scale diverges. -/
theorem tendsto_gaussianPaperLogScale_atTop :
    Filter.Tendsto gaussianPaperLogScale Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [gaussianPaperLogScale] using tendsto_id_div_log_atTop.comp hlog

































































































end ReweightedNPMLE
end

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- All non-entropy approximation terms can be absorbed in the same
`(log n / log log n)^d log n / n` rate. -/
theorem solution
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) +
        4 * (Real.log (gaussianNetCardBound d
            (gaussianPaperMomentOrder 256 n)
            (gaussianPaperWeightDenominator d 256 n) S
            (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2) / n ≤
      gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
        Real.log (n : ℝ) / n := by
  filter_upwards [eventually_gaussianNetHellingerSqError_256_le d hS,
    eventually_log_gaussianNetCardBound_paper_le d
      (show (0 : ℝ) < 256 by norm_num) hS,
    tendsto_gaussianPaperLogScale_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hnet hent hscale hlog hn
  let E := gaussianPaperEntropyConstant d
  let q := gaussianPaperLogScale n ^ d * Real.log (n : ℝ)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog' : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    simpa only [Function.comp_apply] using hlog
  have hscalePow : (1 : ℝ) ≤ gaussianPaperLogScale n ^ d :=
    one_le_pow₀ hscale
  have hq : 1 ≤ q := by
    dsimp [q]
    have hmul := mul_le_mul hscalePow hlog' (by norm_num)
      (show (0 : ℝ) ≤ gaussianPaperLogScale n ^ d by positivity)
    simpa only [one_mul] using hmul
  have hent' : Real.log (gaussianNetCardBound d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) : ℝ) ≤ E * q := by
    dsimp [E, q, gaussianPaperEntropyConstant]
    norm_num at hent ⊢
    convert hent using 1 <;> ring
  have hB : (b + 2) * Real.log (n : ℝ) + 2 ≤ (b + 4) * q := by
    calc
      (b + 2) * Real.log (n : ℝ) + 2 ≤
          (b + 4) * Real.log (n : ℝ) := by nlinarith
      _ ≤ (b + 4) * q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [q]
        have hlog0 : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog'
        have := mul_le_mul_of_nonneg_right hscalePow hlog0
        simpa only [one_mul] using this
  have hsum : Real.log (gaussianNetCardBound d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) : ℝ) +
      (b + 2) * Real.log (n : ℝ) + 2 ≤ (E + b + 4) * q := by
    calc
      Real.log (gaussianNetCardBound d
          (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2 ≤ E * q + (b + 4) * q := by
        linarith
      _ = (E + b + 4) * q := by ring
  have hnetTwo : 2 * gaussianNetHellingerSqError d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) ≤ 22 / (n : ℝ) := by
    calc
      2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) ≤ 2 * (11 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnet (by norm_num)
      _ = 22 / (n : ℝ) := by ring
  calc
    2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) +
        4 * (Real.log (gaussianNetCardBound d
            (gaussianPaperMomentOrder 256 n)
            (gaussianPaperWeightDenominator d 256 n) S
            (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2) / n ≤
      22 / (n : ℝ) + 4 * ((E + b + 4) * q) / n := by
        exact add_le_add hnetTwo
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (by norm_num)) hnreal.le)
    _ = (22 + 4 * (E + b + 4) * q) / (n : ℝ) := by ring
    _ ≤ (22 * q + 4 * (E + b + 4) * q) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnreal.le
      nlinarith
    _ = gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
        Real.log (n : ℝ) / n := by
      dsimp [gaussianPaperRateConstant, E, q]
      ring
