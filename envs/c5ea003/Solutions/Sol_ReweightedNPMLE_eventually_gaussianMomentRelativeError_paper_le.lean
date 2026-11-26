-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianMomentRelativeError_paper_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:09.275425+00:00
-- url     : https://prove2.me/submissions/f8076eb6-23f3-4ba6-90e4-63a99bba7377

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
import Theorems.Thm_ReweightedNPMLE_eventually_exp_two_gaussianPaperTaylorArgument_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStirlingBase_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperStirlingPower_le
import Theorems.Thm_ReweightedNPMLE_pow_div_factorial_le_stirling

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



































/-- The paper Taylor argument is eventually nonnegative. -/
theorem eventually_gaussianPaperTaylorArgument_nonneg
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ gaussianPaperTaylorArgument d S b n := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 0] with n hn
  unfold gaussianPaperTaylorArgument gaussianPaperSampleRadius
    gaussianPaperRadiusExponent
  positivity







































/-- The local relative-density Taylor error with its factorial eliminated by
the effective Stirling bound. -/
theorem gaussianMomentRelativeError_le_stirling {T S : ℝ}
    (hA : 0 ≤ T * S + S ^ 2 / 2) (L : ℕ) :
    gaussianMomentRelativeError T S L ≤
      2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          (Real.exp 1 * (T * S + S ^ 2 / 2) / (L + 1)) ^ (L + 1) := by
  unfold gaussianMomentRelativeError
  have hratio :
      (T * S + S ^ 2 / 2) ^ (L + 1) / ((L + 1).factorial : ℝ) ≤
        (Real.exp 1 * (T * S + S ^ 2 / 2) / (L + 1)) ^ (L + 1) := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      (pow_div_factorial_le_stirling hA (Nat.zero_lt_succ L))
  exact mul_le_mul_of_nonneg_left hratio (by positivity)

































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
/-- Explicit inverse-power bound for the local relative-density Taylor
error.  Choosing `C > 8` makes the exponent negative. -/
theorem solution
    (d : ℕ) {C S b : ℝ} (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) ≤
        2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
  filter_upwards [eventually_gaussianPaperTaylorArgument_nonneg d hS hb,
    eventually_gaussianPaperStirlingBase_le d hC hS hb,
    eventually_gaussianPaperStirlingPower_le hC,
    eventually_exp_two_gaussianPaperTaylorArgument_le d hS hb,
    Filter.eventually_ge_atTop (1 : ℕ)]
      with n hA0 hbase hpower hexp hn
  let A := gaussianPaperTaylorArgument d S b n
  let L := gaussianPaperMomentOrder C n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase0 : 0 ≤ Real.exp 1 * A / ((L : ℝ) + 1) := by positivity
  have hpowBase :
      (Real.exp 1 * A / ((L : ℝ) + 1)) ^ (L + 1) ≤
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
    apply pow_le_pow_left₀ hbase0
    simpa only [A, L] using hbase
  have hstirling := gaussianMomentRelativeError_le_stirling hA0 L
  calc
    gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S L ≤
        2 * Real.exp (2 * A) *
          (Real.exp 1 * A / ((L : ℝ) + 1)) ^ (L + 1) := by
      simpa only [A, L, gaussianPaperTaylorArgument] using hstirling
    _ ≤ 2 * Real.exp (2 * A) *
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
      gcongr
    _ ≤ 2 * (n : ℝ) *
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
      gcongr
    _ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ) := by
      gcongr
    _ = 2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
      calc
        2 * (n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ) =
            2 * ((n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ)) := by ring
        _ = 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ)) := by
          rw [Real.rpow_one]
        _ = 2 * (n : ℝ) ^ ((1 : ℝ) + (-C / 8 : ℝ)) := by
          rw [Real.rpow_add hnreal]
        _ = 2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by ring_nf
