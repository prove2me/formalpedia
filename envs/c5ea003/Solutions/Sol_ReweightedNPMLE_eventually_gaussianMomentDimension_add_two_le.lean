-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianMomentDimension_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:09:31.872666+00:00
-- url     : https://prove2.me/submissions/f9585015-3fef-44e2-bd03-ba75b858d930

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
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentDimension_le_logScale_pow
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperLogScale_nonneg_le_log

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

















































/-- A coarser log-power form, convenient for entropy estimates. -/
theorem eventually_gaussianMomentDimension_le_log_pow
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        (4 * C + 1) ^ d * Real.log (n : ℝ) ^ d := by
  filter_upwards [eventually_gaussianMomentDimension_le_logScale_pow d hC,
    eventually_gaussianPaperLogScale_nonneg_le_log] with n hk hs
  calc
    (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        ((4 * C + 1) * gaussianPaperLogScale n) ^ d := hk
    _ = (4 * C + 1) ^ d * gaussianPaperLogScale n ^ d := by rw [mul_pow]
    _ ≤ (4 * C + 1) ^ d * Real.log (n : ℝ) ^ d := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hs.1 hs.2 d) (by positivity)



























































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
/-- In particular, the polylogarithmic moment dimension is eventually at
most the sample size (with room for two rounding slots). -/
theorem solution
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) + 2 ≤ n := by
  let A : ℝ := (4 * C + 1) ^ d
  have hsmall0 : (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_pow_log_id_atTop.comp_tendsto
        tendsto_natCast_atTop_atTop)
  have hsmall : (fun n : ℕ ↦ A * Real.log (n : ℝ) ^ d) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := hsmall0.const_mul_left A
  have hhalf := hsmall.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [eventually_gaussianMomentDimension_le_log_pow d hC,
    hhalf, Filter.eventually_ge_atTop (4 : ℕ)] with n hk hnsmall hnfour
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlogpow : 0 ≤ Real.log (n : ℝ) ^ d := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hlogpow),
    abs_of_nonneg hn0] at hnsmall
  have hnfourReal : (4 : ℝ) ≤ n := by exact_mod_cast hnfour
  dsimp [A] at hnsmall
  nlinarith
