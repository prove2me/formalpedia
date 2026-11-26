-- Prove2me | solution 1 for ReweightedNPMLE.eventually_gaussianPaperStirlingBase_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:07:14.360154+00:00
-- url     : https://prove2.me/submissions/7879715c-7387-441e-9254-d5e82177ab59

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
import Theorems.Thm_ReweightedNPMLE_eventually_const_mul_log_log_le_log_rpow
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaperTaylorArgument_le

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































theorem gaussianPaperTaylorConstant_nonneg (d : ℕ) {S b : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) :
    0 ≤ gaussianPaperTaylorConstant d S b := by
  unfold gaussianPaperTaylorConstant
  positivity



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
/-- The Stirling base for the local Taylor remainder is eventually at most
`(log n)⁻¹ᐟ⁸`. -/
theorem solution
    (d : ℕ) {C S b : ℝ} (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp 1 * gaussianPaperTaylorArgument d S b n /
          ((gaussianPaperMomentOrder C n : ℝ) + 1) ≤
        Real.log (n : ℝ) ^ (-1 / 8 : ℝ) := by
  let D := gaussianPaperTaylorConstant d S b
  have hD : 0 ≤ D := gaussianPaperTaylorConstant_nonneg d hS hb
  have hcoef : 0 ≤ Real.exp 1 * D / C := by positivity
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_gaussianPaperTaylorArgument_le d hS hb,
    eventually_gaussianPaperTaylorArgument_nonneg d hS hb,
    eventually_const_mul_log_log_le_log_rpow hcoef,
    hlog.eventually_ge_atTop 1, hloglog.eventually_gt_atTop 0]
      with n hA hA0 hsmall hlogn hloglogn
  let x := Real.log (n : ℝ)
  let y := Real.log x
  let L := gaussianPaperMomentOrder C n
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hlogn
  have hy : 0 < y := by simpa only [x, y] using hloglogn
  have hceil : C * (x / y) ≤ (L : ℝ) := by
    simpa only [L, gaussianPaperMomentOrder, gaussianPaperLogScale, x, y] using
      (Nat.le_ceil (C * gaussianPaperLogScale n))
  have hscale : 0 < C * (x / y) := mul_pos hC (div_pos hx hy)
  have hden : 0 < (L : ℝ) + 1 := by positivity
  have hnum : 0 ≤ Real.exp 1 * D * Real.sqrt x := by positivity
  have hsmall' : (Real.exp 1 * D / C) * y ≤ x ^ (3 / 8 : ℝ) := by
    simpa only [D, x, y] using hsmall
  calc
    Real.exp 1 * gaussianPaperTaylorArgument d S b n / ((L : ℝ) + 1) ≤
        Real.exp 1 * (D * Real.sqrt x) / ((L : ℝ) + 1) := by
      gcongr
    _ = (Real.exp 1 * D * Real.sqrt x) / ((L : ℝ) + 1) := by ring
    _ ≤ (Real.exp 1 * D * Real.sqrt x) / (C * (x / y)) :=
      div_le_div_of_nonneg_left hnum hscale (by linarith)
    _ = ((Real.exp 1 * D / C) * y) * Real.sqrt x / x := by
      field_simp
      <;> ring
    _ ≤ x ^ (3 / 8 : ℝ) * Real.sqrt x / x := by
      gcongr
    _ = x ^ (-1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      have hsub : x ^ ((3 / 8 : ℝ) + 1 / 2 - 1) =
          x ^ ((3 / 8 : ℝ) + 1 / 2) / x := by
        simpa only [Real.rpow_one] using
          Real.rpow_sub hx ((3 / 8 : ℝ) + 1 / 2) 1
      rw [← hsub]
      norm_num
    _ = Real.log (n : ℝ) ^ (-1 / 8 : ℝ) := rfl
