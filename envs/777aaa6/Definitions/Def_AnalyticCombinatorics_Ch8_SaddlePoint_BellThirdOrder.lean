-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellThirdOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_BellThirdOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:32:27.499997+00:00
-- url     : https://prove2.me/theorems/51824e97-d079-45ac-b9b8-33f71455d310
-- title:
--   Bell additional correction with unchanged robust scale
-- statement:
--   The fifth and sixth logarithmic saddle functions are explicit Touchard polynomials times exp(r). bellThirdCorrScale is exactly bellSecondCorrScale. A Gaussian polynomial dominator and the supplied Bell third-order record implement the additional polynomial correction at that same robust scale.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/BellThirdOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Third-order saddle data for Bell numbers

This file instantiates the third-order Hayman wrapper for
`exp (exp z - 1)`.  The fifth and sixth logarithmic saddle derivatives are
the next two Touchard polynomials evaluated at the Bell saddle.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

/-- Fifth logarithmic saddle derivative for Bell numbers. -/
def bellSaddleB5Real (r : ℝ) : ℝ :=
  (r + 15 * r ^ 2 + 25 * r ^ 3 + 10 * r ^ 4 + r ^ 5) * Real.exp r

/-- Sixth logarithmic saddle derivative for Bell numbers. -/
def bellSaddleB6Real (r : ℝ) : ℝ :=
  (r + 31 * r ^ 2 + 90 * r ^ 3 + 65 * r ^ 4 + 15 * r ^ 5 + r ^ 6) *
    Real.exp r

/--
Robust third-order scale for the current abstract interface.  The generic
third-order scale includes the second-order coefficient scale, so the Bell
second-order scale is the reusable normalizer here.
-/
def bellThirdCorrScale (r : ℝ) : ℝ :=
  bellSecondCorrScale r

private lemma bellSaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < bellSaddleBReal r := by
  unfold bellSaddleBReal
  positivity

private lemma bell_b_ge_rsq_exp {r : ℝ} (hr : 1 ≤ r) :
    r ^ 2 * Real.exp r ≤ bellSaddleBReal r := by
  unfold bellSaddleBReal
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hpoly : r ^ 2 ≤ r * (r + 1) := by nlinarith [hr0]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le

private lemma bell_sqrtB_ge_r_exp_half {r : ℝ} (hr : 1 ≤ r) :
    r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hsq :
      (r * Real.exp (r / 2)) ^ 2 ≤ bellSaddleBReal r := by
    unfold bellSaddleBReal
    rw [Real.exp_half]
    have hpoly : r ^ 2 ≤ r * (r + 1) := by nlinarith [hr0]
    calc
      (r * Real.sqrt (Real.exp r)) ^ 2 = r ^ 2 * Real.exp r := by
        rw [mul_pow, Real.sq_sqrt (Real.exp_pos r).le]
      _ ≤ (r * (r + 1)) * Real.exp r :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le
  exact Real.le_sqrt_of_sq_le hsq

private lemma bell_b_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(bellSaddleBReal r : ℂ)‖ = bellSaddleBReal r := by
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]

private lemma bell_sqrtB_norm_eq_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    ‖(Real.sqrt (bellSaddleBReal r) : ℂ)‖ =
      Real.sqrt (bellSaddleBReal r) := by
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (bellSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos]

private lemma bell_b3_nonneg_of_ge_one {r : ℝ} (_hr : 1 ≤ r) :
    0 ≤ bellSaddleB3Real r := by
  unfold bellSaddleB3Real
  positivity

private lemma bell_b4_nonneg_of_ge_one {r : ℝ} (_hr : 1 ≤ r) :
    0 ≤ bellSaddleB4Real r := by
  unfold bellSaddleB4Real
  positivity

private lemma bell_b5_nonneg_of_ge_one {r : ℝ} (_hr : 1 ≤ r) :
    0 ≤ bellSaddleB5Real r := by
  unfold bellSaddleB5Real
  positivity

private lemma bell_b6_nonneg_of_ge_one {r : ℝ} (_hr : 1 ≤ r) :
    0 ≤ bellSaddleB6Real r := by
  unfold bellSaddleB6Real
  positivity

private lemma bell_b3_le {r : ℝ} (hr : 1 ≤ r) :
    bellSaddleB3Real r ≤ 5 * r ^ 3 * Real.exp r := by
  unfold bellSaddleB3Real
  have hpoly : r + 3 * r ^ 2 + r ^ 3 ≤ 5 * r ^ 3 := by
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le

private lemma bell_b4_le {r : ℝ} (hr : 1 ≤ r) :
    bellSaddleB4Real r ≤ 15 * r ^ 4 * Real.exp r := by
  unfold bellSaddleB4Real
  have hpoly : r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4 ≤ 15 * r ^ 4 := by
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
      show 0 ≤ r ^ 4 by positivity]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le

private lemma bell_b5_le {r : ℝ} (hr : 1 ≤ r) :
    bellSaddleB5Real r ≤ 100 * r ^ 5 * Real.exp r := by
  unfold bellSaddleB5Real
  have hpoly :
      r + 15 * r ^ 2 + 25 * r ^ 3 + 10 * r ^ 4 + r ^ 5 ≤ 100 * r ^ 5 := by
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
      show 0 ≤ r ^ 4 by positivity, show 0 ≤ r ^ 5 by positivity]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le

private lemma bell_b6_le {r : ℝ} (hr : 1 ≤ r) :
    bellSaddleB6Real r ≤ 250 * r ^ 6 * Real.exp r := by
  unfold bellSaddleB6Real
  have hpoly :
      r + 31 * r ^ 2 + 90 * r ^ 3 + 65 * r ^ 4 + 15 * r ^ 5 + r ^ 6 ≤
        250 * r ^ 6 := by
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
      show 0 ≤ r ^ 4 by positivity, show 0 ≤ r ^ 5 by positivity,
      show 0 ≤ r ^ 6 by positivity]
  exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le

private lemma bell_exp_neg_two_le_neg_one {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-(2 * r)) ≤ Real.exp (-r) := by
  exact Real.exp_le_exp.mpr (by nlinarith)

private lemma bell_exp_neg_two_le_neg_three_halves {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-(2 * r)) ≤ Real.exp (-(3 / 2 : ℝ) * r) := by
  exact Real.exp_le_exp.mpr (by nlinarith)

private lemma bell_exp_mul_two (r : ℝ) :
    Real.exp (r * 2) = (Real.exp r) ^ 2 := by
  rw [show r * 2 = 2 * r by ring]
  rw [← Real.exp_nat_mul]
  ring_nf

private lemma bell_exp_pow_three (r : ℝ) :
    (Real.exp r) ^ 3 = Real.exp (r * 3) := by
  rw [show r * 3 = 3 * r by ring]
  rw [← Real.exp_nat_mul]
  ring_nf

private lemma bell_corr_term_b6_le_exp {r : ℝ} (hr : 1 ≤ r) :
    |bellSaddleB6Real r| / (bellSaddleBReal r) ^ 3 ≤ 1000 * Real.exp (-r) := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb3_ge : (r ^ 2 * Real.exp r) ^ 3 ≤ (bellSaddleBReal r) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 3
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    |bellSaddleB6Real r| / (bellSaddleBReal r) ^ 3
        = bellSaddleB6Real r / (bellSaddleBReal r) ^ 3 := by
          rw [abs_of_nonneg (bell_b6_nonneg_of_ge_one hr)]
    _ ≤ (250 * r ^ 6 * Real.exp r) / (r ^ 2 * Real.exp r) ^ 3 := by
          exact div_le_div₀ (by positivity) (bell_b6_le hr) (by positivity)
            hb3_ge
    _ = 250 * Real.exp (-(2 * r)) := by
          have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
          have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          field_simp [hrpos.ne', hexp_ne]
          ring_nf
          rw [Real.exp_neg, sq]
          field_simp [hexp_ne]
          rw [bell_exp_mul_two]
    _ ≤ 1000 * Real.exp (-r) := by
          calc
            250 * Real.exp (-(2 * r)) ≤ 250 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (bell_exp_neg_two_le_neg_one hr0)
                (by norm_num)
            _ ≤ 1000 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

private lemma bell_corr_term_b3b5_le_exp {r : ℝ} (hr : 1 ≤ r) :
    |bellSaddleB3Real r * bellSaddleB5Real r| / (bellSaddleBReal r) ^ 4 ≤
      1000 * Real.exp (-r) := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb4_ge : (r ^ 2 * Real.exp r) ^ 4 ≤ (bellSaddleBReal r) ^ 4 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 4
  have hnum_nonneg : 0 ≤ bellSaddleB3Real r * bellSaddleB5Real r :=
    mul_nonneg (bell_b3_nonneg_of_ge_one hr) (bell_b5_nonneg_of_ge_one hr)
  have hnum_le :
      bellSaddleB3Real r * bellSaddleB5Real r ≤
        500 * r ^ 8 * (Real.exp r) ^ 2 := by
    calc
      bellSaddleB3Real r * bellSaddleB5Real r
          ≤ (5 * r ^ 3 * Real.exp r) * (100 * r ^ 5 * Real.exp r) :=
            mul_le_mul (bell_b3_le hr) (bell_b5_le hr)
              (bell_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 500 * r ^ 8 * (Real.exp r) ^ 2 := by ring
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    |bellSaddleB3Real r * bellSaddleB5Real r| / (bellSaddleBReal r) ^ 4
        = (bellSaddleB3Real r * bellSaddleB5Real r) / (bellSaddleBReal r) ^ 4 := by
          rw [abs_of_nonneg hnum_nonneg]
    _ ≤ (500 * r ^ 8 * (Real.exp r) ^ 2) / (r ^ 2 * Real.exp r) ^ 4 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hb4_ge
    _ = 500 * Real.exp (-(2 * r)) := by
          have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
          have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          field_simp [hrpos.ne', hexp_ne]
          ring_nf
          rw [Real.exp_neg, sq]
          field_simp [hexp_ne]
          rw [bell_exp_mul_two]
    _ ≤ 1000 * Real.exp (-r) := by
          calc
            500 * Real.exp (-(2 * r)) ≤ 500 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (bell_exp_neg_two_le_neg_one hr0)
                (by norm_num)
            _ ≤ 1000 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

private lemma bell_corr_term_b4sq_le_exp {r : ℝ} (hr : 1 ≤ r) :
    (bellSaddleB4Real r) ^ 2 / (bellSaddleBReal r) ^ 4 ≤
      1000 * Real.exp (-r) := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb4_ge : (r ^ 2 * Real.exp r) ^ 4 ≤ (bellSaddleBReal r) ^ 4 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 4
  have hnum_le :
      (bellSaddleB4Real r) ^ 2 ≤ 225 * r ^ 8 * (Real.exp r) ^ 2 := by
    calc
      (bellSaddleB4Real r) ^ 2 ≤ (15 * r ^ 4 * Real.exp r) ^ 2 :=
        pow_le_pow_left₀ (bell_b4_nonneg_of_ge_one hr) (bell_b4_le hr) 2
      _ = 225 * r ^ 8 * (Real.exp r) ^ 2 := by ring
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    (bellSaddleB4Real r) ^ 2 / (bellSaddleBReal r) ^ 4
        ≤ (225 * r ^ 8 * (Real.exp r) ^ 2) / (r ^ 2 * Real.exp r) ^ 4 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hb4_ge
    _ = 225 * Real.exp (-(2 * r)) := by
          have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
          have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          field_simp [hrpos.ne', hexp_ne]
          ring_nf
          rw [Real.exp_neg, sq]
          field_simp [hexp_ne]
          rw [bell_exp_mul_two]
    _ ≤ 1000 * Real.exp (-r) := by
          calc
            225 * Real.exp (-(2 * r)) ≤ 225 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (bell_exp_neg_two_le_neg_one hr0)
                (by norm_num)
            _ ≤ 1000 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

private lemma bell_corr_term_b3sqb4_le_exp {r : ℝ} (hr : 1 ≤ r) :
    (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| / (bellSaddleBReal r) ^ 5 ≤
      1000 * Real.exp (-r) := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb5_ge : (r ^ 2 * Real.exp r) ^ 5 ≤ (bellSaddleBReal r) ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 5
  have hb4_nonneg : 0 ≤ bellSaddleB4Real r := bell_b4_nonneg_of_ge_one hr
  have hnum_le :
      (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| ≤
        375 * r ^ 10 * (Real.exp r) ^ 3 := by
    rw [abs_of_nonneg hb4_nonneg]
    have hb3sq :
        (bellSaddleB3Real r) ^ 2 ≤ (5 * r ^ 3 * Real.exp r) ^ 2 :=
      pow_le_pow_left₀ (bell_b3_nonneg_of_ge_one hr) (bell_b3_le hr) 2
    calc
      (bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r
          ≤ (5 * r ^ 3 * Real.exp r) ^ 2 * (15 * r ^ 4 * Real.exp r) :=
            mul_le_mul hb3sq (bell_b4_le hr) (bell_b4_nonneg_of_ge_one hr)
              (by positivity)
      _ = 375 * r ^ 10 * (Real.exp r) ^ 3 := by ring
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| / (bellSaddleBReal r) ^ 5
        ≤ (375 * r ^ 10 * (Real.exp r) ^ 3) / (r ^ 2 * Real.exp r) ^ 5 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hb5_ge
    _ = 375 * Real.exp (-(2 * r)) := by
          have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
          have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          field_simp [hrpos.ne', hexp_ne]
          ring_nf
          rw [Real.exp_neg, sq]
          field_simp [hexp_ne]
          rw [bell_exp_mul_two]
    _ ≤ 1000 * Real.exp (-r) := by
          calc
            375 * Real.exp (-(2 * r)) ≤ 375 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (bell_exp_neg_two_le_neg_one hr0)
                (by norm_num)
            _ ≤ 1000 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

private lemma bell_corr_term_b3four_le_exp {r : ℝ} (hr : 1 ≤ r) :
    (bellSaddleB3Real r) ^ 4 / (bellSaddleBReal r) ^ 6 ≤
      1000 * Real.exp (-r) := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb6_ge : (r ^ 2 * Real.exp r) ^ 6 ≤ (bellSaddleBReal r) ^ 6 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 6
  have hnum_le :
      (bellSaddleB3Real r) ^ 4 ≤ 625 * r ^ 12 * (Real.exp r) ^ 4 := by
    calc
      (bellSaddleB3Real r) ^ 4 ≤ (5 * r ^ 3 * Real.exp r) ^ 4 :=
        pow_le_pow_left₀ (bell_b3_nonneg_of_ge_one hr) (bell_b3_le hr) 4
      _ = 625 * r ^ 12 * (Real.exp r) ^ 4 := by ring
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  calc
    (bellSaddleB3Real r) ^ 4 / (bellSaddleBReal r) ^ 6
        ≤ (625 * r ^ 12 * (Real.exp r) ^ 4) / (r ^ 2 * Real.exp r) ^ 6 := by
          exact div_le_div₀ (by positivity) hnum_le (by positivity) hb6_ge
    _ = 625 * Real.exp (-(2 * r)) := by
          have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
          have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
          field_simp [hrpos.ne', hexp_ne]
          ring_nf
          rw [Real.exp_neg, sq]
          field_simp [hexp_ne]
          rw [bell_exp_mul_two]
    _ ≤ 1000 * Real.exp (-r) := by
          calc
            625 * Real.exp (-(2 * r)) ≤ 625 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_left (bell_exp_neg_two_le_neg_one hr0)
                (by norm_num)
            _ ≤ 1000 * Real.exp (-r) :=
              mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le

lemma bell_saddleThirdCorrectionScale_le_second :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in atTop,
        saddleThirdCorrectionScale bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r ≤ K * bellThirdCorrScale r := by
  refine ⟨50000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), bellSecondCorrScale_lower_exp_eventually,
      bellSecondCorrScale_pos_eventually] with r hr hsecondLower hsecondPos
  have hterm₁ := bell_corr_term_b6_le_exp (r := r) hr
  have hterm₂ := bell_corr_term_b3b5_le_exp (r := r) hr
  have hterm₃ := bell_corr_term_b4sq_le_exp (r := r) hr
  have hterm₄ := bell_corr_term_b3sqb4_le_exp (r := r) hr
  have hterm₅ := bell_corr_term_b3four_le_exp (r := r) hr
  have hexp_nonneg : 0 ≤ Real.exp (-r) := (Real.exp_pos _).le
  have hthird :
      |bellSaddleB6Real r| / (bellSaddleBReal r) ^ 3
        + |bellSaddleB3Real r * bellSaddleB5Real r| / (bellSaddleBReal r) ^ 4
        + (bellSaddleB4Real r) ^ 2 / (bellSaddleBReal r) ^ 4
        + (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| /
            (bellSaddleBReal r) ^ 5
        + (bellSaddleB3Real r) ^ 4 / (bellSaddleBReal r) ^ 6
        ≤ 5000 * Real.exp (-r) := by
    nlinarith
  have hthird_second :
      |bellSaddleB6Real r| / (bellSaddleBReal r) ^ 3
        + |bellSaddleB3Real r * bellSaddleB5Real r| / (bellSaddleBReal r) ^ 4
        + (bellSaddleB4Real r) ^ 2 / (bellSaddleBReal r) ^ 4
        + (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| /
            (bellSaddleBReal r) ^ 5
        + (bellSaddleB3Real r) ^ 4 / (bellSaddleBReal r) ^ 6
        ≤ 40000 * bellSecondCorrScale r := by
    have hscale : 5000 * Real.exp (-r) ≤ 40000 * bellSecondCorrScale r := by
      nlinarith
    exact hthird.trans hscale
  unfold bellThirdCorrScale
  change
    bellSecondCorrScale r +
          |bellSaddleB6Real r| / (bellSaddleBReal r) ^ 3
        + |bellSaddleB3Real r * bellSaddleB5Real r| / (bellSaddleBReal r) ^ 4
        + (bellSaddleB4Real r) ^ 2 / (bellSaddleBReal r) ^ 4
        + (bellSaddleB3Real r) ^ 2 * |bellSaddleB4Real r| /
            (bellSaddleBReal r) ^ 5
        + (bellSaddleB3Real r) ^ 4 / (bellSaddleBReal r) ^ 6
      ≤ 50000 * bellSecondCorrScale r
  nlinarith [hthird_second, hsecondPos.le]

private def bellThirdGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12)

private lemma bellThirdGaussianDom_nonneg (x : ℝ) : 0 ≤ bellThirdGaussianDom x := by
  unfold bellThirdGaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable_third (k : ℕ) :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ k) := by
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hk : (-1 : ℝ) < (k : ℝ) := by linarith
  have hbase : Integrable (fun x : ℝ => x ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2) hk)
  have hbase2 : Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ k) := by
    convert hbase using 1
    ext x
    ring_nf
  have hnorm := hbase2.norm
  convert hnorm using 1
  ext x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]

private lemma bellThirdGaussianDom_integrable : Integrable bellThirdGaussianDom := by
  unfold bellThirdGaussianDom
  have hsum :
      Integrable
        (((((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 5) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 6)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 7)) +
          (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 8)) +
          ((fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 9) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 10) +
            (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * |x| ^ 12))) :=
    ((((gaussian_abs_monomial_integrable_third 5).add
      (gaussian_abs_monomial_integrable_third 6)).add
      (gaussian_abs_monomial_integrable_third 7)).add
      (gaussian_abs_monomial_integrable_third 8)).add
      (((gaussian_abs_monomial_integrable_third 9).add
        (gaussian_abs_monomial_integrable_third 10)).add
        (gaussian_abs_monomial_integrable_third 12))
  convert hsum using 1
  ext x
  simp only [Pi.add_apply]
  ring_nf

private lemma bellThirdGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, bellThirdGaussianDom x := by
  exact integral_nonneg (fun x => bellThirdGaussianDom_nonneg x)

private lemma bellThirdGaussianDom_continuous : Continuous bellThirdGaussianDom := by
  unfold bellThirdGaussianDom
  fun_prop

private lemma bellThirdGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, bellThirdGaussianDom x) ≤ ∫ x : ℝ, bellThirdGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral bellThirdGaussianDom_integrable
    (Eventually.of_forall bellThirdGaussianDom_nonneg)

private lemma bell_third_extra5_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((bellSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 := by
  set_option backward.isDefEq.respectTransparency false in
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (bellSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hsqrt_ge : r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) :=
      bell_sqrtB_ge_r_exp_half hr
    have hsqrt5_ge :
        (r * Real.exp (r / 2)) ^ 5 ≤ (Real.sqrt (bellSaddleBReal r)) ^ 5 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ r * Real.exp (r / 2)) hsqrt_ge 5
    have hcoef :
        ‖(bellSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)‖ ≤
          10 * Real.exp (-(3 / 2 : ℝ) * r) := by
      calc
        ‖(bellSaddleB5Real r : ℂ) /
            (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)‖
            = bellSaddleB5Real r /
                (120 * (Real.sqrt (bellSaddleBReal r)) ^ 5) := by
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (bell_b5_nonneg_of_ge_one hr)]
              simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
              rw [abs_of_pos hsqrt_pos]
        _ ≤ (100 * r ^ 5 * Real.exp r) /
                (120 * (r * Real.exp (r / 2)) ^ 5) := by
              exact div_le_div₀ (by positivity) (bell_b5_le hr) (by positivity)
                (by nlinarith [hsqrt5_ge])
        _ = (5 / 6 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) := by
              have hexp_half_ne : Real.exp (r / 2) ≠ 0 := (Real.exp_pos _).ne'
              field_simp [hrpos.ne', hexp_half_ne]
              have hexp_pow5 :
                  (Real.exp (r / 2)) ^ 5 = Real.exp (5 * (r / 2)) := by
                rw [← Real.exp_nat_mul]
                norm_num
              rw [hexp_pow5]
              ring_nf
              rw [← Real.exp_add]
              ring_nf
        _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
              mul_le_mul_of_nonneg_right (by norm_num : (5 / 6 : ℝ) ≤ 10)
                (Real.exp_pos _).le
    calc
      ‖Complex.I * ((bellSaddleB5Real r : ℂ) /
        (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5‖
          = ‖(bellSaddleB5Real r : ℂ) /
              (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)‖ * |x| ^ 5 := by
            rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs]
      _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 5 :=
            mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 5)
      _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 := by ring

private lemma bell_third_extra6_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((bellSaddleB6Real r : ℂ) / (720 * (bellSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 6 := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb3_ge : (r ^ 2 * Real.exp r) ^ 3 ≤ (bellSaddleBReal r) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 3
  have hcoef :
      ‖(bellSaddleB6Real r : ℂ) / (720 * (bellSaddleBReal r : ℂ) ^ 3)‖
        ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖(bellSaddleB6Real r : ℂ) / (720 * (bellSaddleBReal r : ℂ) ^ 3)‖
          = bellSaddleB6Real r / (720 * (bellSaddleBReal r) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (bell_b6_nonneg_of_ge_one hr)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_b_norm_eq_of_ge_one hr]
      _ ≤ (250 * r ^ 6 * Real.exp r) / (720 * (r ^ 2 * Real.exp r) ^ 3) := by
            exact div_le_div₀ (by positivity) (bell_b6_le hr) (by positivity)
              (by nlinarith [hb3_ge])
      _ = (25 / 72 : ℝ) * Real.exp (-(2 * r)) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hrpos.ne', hexp_ne]
            ring_nf
            rw [Real.exp_neg, sq]
            field_simp [hexp_ne]
            rw [bell_exp_mul_two]
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hr0 : 0 ≤ r := le_trans zero_le_one hr
            calc
              (25 / 72 : ℝ) * Real.exp (-(2 * r))
                  ≤ (25 / 72 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_left
                      (bell_exp_neg_two_le_neg_three_halves hr0) (by norm_num)
              _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  calc
    ‖((bellSaddleB6Real r : ℂ) / (720 * (bellSaddleBReal r : ℂ) ^ 3)) *
        (x : ℂ) ^ 6‖
        = ‖(bellSaddleB6Real r : ℂ) /
            (720 * (bellSaddleBReal r : ℂ) ^ 3)‖ * |x| ^ 6 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 6 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 6)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 6 := by ring

private lemma bell_third_extra7_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * (((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
        (bellSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 7 := by
  have hsqrt_ge : r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) :=
    bell_sqrtB_ge_r_exp_half hr
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hsqrt3_ge :
      (r * Real.exp (r / 2)) ^ 3 ≤ (Real.sqrt (bellSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r * Real.exp (r / 2)) hsqrt_ge 3
  have hb2_ge : (r ^ 2 * Real.exp r) ^ 2 ≤ (bellSaddleBReal r) ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 2
  have hden_ge :
      (r * Real.exp (r / 2)) ^ 3 * (r ^ 2 * Real.exp r) ^ 2 ≤
        (Real.sqrt (bellSaddleBReal r)) ^ 3 * (bellSaddleBReal r) ^ 2 :=
    mul_le_mul hsqrt3_ge hb2_ge (by positivity) (by positivity)
  have hnum_nonneg : 0 ≤ bellSaddleB3Real r * bellSaddleB4Real r :=
    mul_nonneg (bell_b3_nonneg_of_ge_one hr) (bell_b4_nonneg_of_ge_one hr)
  have hnum_le :
      bellSaddleB3Real r * bellSaddleB4Real r ≤
        75 * r ^ 7 * (Real.exp r) ^ 2 := by
    calc
      bellSaddleB3Real r * bellSaddleB4Real r
          ≤ (5 * r ^ 3 * Real.exp r) * (15 * r ^ 4 * Real.exp r) :=
            mul_le_mul (bell_b3_le hr) (bell_b4_le hr)
              (bell_b4_nonneg_of_ge_one hr) (by positivity)
      _ = 75 * r ^ 7 * (Real.exp r) ^ 2 := by ring
  have hcoef :
      ‖(((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
          (bellSaddleBReal r : ℂ) ^ 2))‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖(((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
        (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
          (bellSaddleBReal r : ℂ) ^ 2))‖
          =
            (bellSaddleB3Real r * bellSaddleB4Real r) /
              (144 * (Real.sqrt (bellSaddleBReal r)) ^ 3 *
                (bellSaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_sqrtB_norm_eq_of_ge_one hr, bell_b_norm_eq_of_ge_one hr]
      _ ≤ (75 * r ^ 7 * (Real.exp r) ^ 2) /
              (144 * (r * Real.exp (r / 2)) ^ 3 *
                (r ^ 2 * Real.exp r) ^ 2) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hden_ge])
      _ = (25 / 48 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            have hexp_half_ne : Real.exp (r / 2) ≠ 0 := (Real.exp_pos _).ne'
            field_simp [hrpos.ne', hexp_ne, hexp_half_ne]
            have hexp_half_pow3 :
                (Real.exp (r / 2)) ^ 3 = Real.exp (3 * (r / 2)) := by
              rw [← Real.exp_nat_mul]
              norm_num
            rw [hexp_half_pow3]
            ring_nf
            rw [← Real.exp_add]
            ring_nf
            simp
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
            mul_le_mul_of_nonneg_right (by norm_num : (25 / 48 : ℝ) ≤ 10)
              (Real.exp_pos _).le
  calc
    ‖Complex.I * (((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
        (bellSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7‖
        = ‖(((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
            (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
              (bellSaddleBReal r : ℂ) ^ 2))‖ * |x| ^ 7 := by
          rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 7 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 7)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 7 := by ring

private lemma bell_third_extra8a_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
      (720 * (bellSaddleBReal r : ℂ) ^ 4) * (x : ℂ) ^ 8)‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb4_ge : (r ^ 2 * Real.exp r) ^ 4 ≤ (bellSaddleBReal r) ^ 4 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 4
  have hnum_nonneg : 0 ≤ bellSaddleB3Real r * bellSaddleB5Real r :=
    mul_nonneg (bell_b3_nonneg_of_ge_one hr) (bell_b5_nonneg_of_ge_one hr)
  have hnum_le :
      bellSaddleB3Real r * bellSaddleB5Real r ≤
        500 * r ^ 8 * (Real.exp r) ^ 2 := by
    calc
      bellSaddleB3Real r * bellSaddleB5Real r
          ≤ (5 * r ^ 3 * Real.exp r) * (100 * r ^ 5 * Real.exp r) :=
            mul_le_mul (bell_b3_le hr) (bell_b5_le hr)
              (bell_b5_nonneg_of_ge_one hr) (by positivity)
      _ = 500 * r ^ 8 * (Real.exp r) ^ 2 := by ring
  have hcoef :
      ‖(((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
        (720 * (bellSaddleBReal r : ℂ) ^ 4))‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖(((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
        (720 * (bellSaddleBReal r : ℂ) ^ 4))‖
          = (bellSaddleB3Real r * bellSaddleB5Real r) /
              (720 * (bellSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_b_norm_eq_of_ge_one hr]
      _ ≤ (500 * r ^ 8 * (Real.exp r) ^ 2) /
              (720 * (r ^ 2 * Real.exp r) ^ 4) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ = (25 / 36 : ℝ) * Real.exp (-(2 * r)) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hrpos.ne', hexp_ne]
            ring_nf
            rw [Real.exp_neg, sq]
            field_simp [hexp_ne]
            rw [bell_exp_mul_two]
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hr0 : 0 ≤ r := le_trans zero_le_one hr
            calc
              (25 / 36 : ℝ) * Real.exp (-(2 * r))
                  ≤ (25 / 36 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_left
                      (bell_exp_neg_two_le_neg_three_halves hr0) (by norm_num)
              _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  calc
    ‖(((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
      (720 * (bellSaddleBReal r : ℂ) ^ 4) * (x : ℂ) ^ 8)‖
        = ‖(((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
            (720 * (bellSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by ring

private lemma bell_third_extra8b_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (bellSaddleBReal r : ℂ) ^ 4) * (x : ℂ) ^ 8)‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb4_ge : (r ^ 2 * Real.exp r) ^ 4 ≤ (bellSaddleBReal r) ^ 4 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 4
  have hnum_le :
      (bellSaddleB4Real r) ^ 2 ≤ 225 * r ^ 8 * (Real.exp r) ^ 2 := by
    calc
      (bellSaddleB4Real r) ^ 2 ≤ (15 * r ^ 4 * Real.exp r) ^ 2 :=
        pow_le_pow_left₀ (bell_b4_nonneg_of_ge_one hr) (bell_b4_le hr) 2
      _ = 225 * r ^ 8 * (Real.exp r) ^ 2 := by ring
  have hcoef :
      ‖((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (bellSaddleBReal r : ℂ) ^ 4))‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
        (1152 * (bellSaddleBReal r : ℂ) ^ 4))‖
          = (bellSaddleB4Real r) ^ 2 / (1152 * (bellSaddleBReal r) ^ 4) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg _)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_b_norm_eq_of_ge_one hr]
      _ ≤ (225 * r ^ 8 * (Real.exp r) ^ 2) /
              (1152 * (r ^ 2 * Real.exp r) ^ 4) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb4_ge])
      _ = (25 / 128 : ℝ) * Real.exp (-(2 * r)) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hrpos.ne', hexp_ne]
            ring_nf
            rw [Real.exp_neg, sq]
            field_simp [hexp_ne]
            rw [bell_exp_mul_two]
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hr0 : 0 ≤ r := le_trans zero_le_one hr
            calc
              (25 / 128 : ℝ) * Real.exp (-(2 * r))
                  ≤ (25 / 128 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_left
                      (bell_exp_neg_two_le_neg_three_halves hr0) (by norm_num)
              _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  calc
    ‖((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (bellSaddleBReal r : ℂ) ^ 4) * (x : ℂ) ^ 8)‖
        = ‖((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
            (1152 * (bellSaddleBReal r : ℂ) ^ 4))‖ * |x| ^ 8 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 8 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 8)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by ring

private lemma bell_third_extra9_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖Complex.I * ((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 9 := by
  set_option backward.isDefEq.respectTransparency false in
    have hsqrt_ge : r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) :=
      bell_sqrtB_ge_r_exp_half hr
    have hsqrt9_ge :
        (r * Real.exp (r / 2)) ^ 9 ≤ (Real.sqrt (bellSaddleBReal r)) ^ 9 :=
      pow_le_pow_left₀ (by positivity : 0 ≤ r * Real.exp (r / 2)) hsqrt_ge 9
    have hnum_le :
        (bellSaddleB3Real r) ^ 3 ≤ 125 * r ^ 9 * (Real.exp r) ^ 3 := by
      calc
        (bellSaddleB3Real r) ^ 3 ≤ (5 * r ^ 3 * Real.exp r) ^ 3 :=
          pow_le_pow_left₀ (bell_b3_nonneg_of_ge_one hr) (bell_b3_le hr) 3
        _ = 125 * r ^ 9 * (Real.exp r) ^ 3 := by ring
    have hcoef :
        ‖((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
          (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9))‖ ≤
          10 * Real.exp (-(3 / 2 : ℝ) * r) := by
      calc
        ‖((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
          (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9))‖
            = (bellSaddleB3Real r) ^ 3 /
                (1296 * (Real.sqrt (bellSaddleBReal r)) ^ 9) := by
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (pow_nonneg (bell_b3_nonneg_of_ge_one hr) 3)]
              simp only [norm_mul, Complex.norm_ofNat, norm_pow]
              rw [bell_sqrtB_norm_eq_of_ge_one hr]
        _ ≤ (125 * r ^ 9 * (Real.exp r) ^ 3) /
                (1296 * (r * Real.exp (r / 2)) ^ 9) := by
              exact div_le_div₀ (by positivity) hnum_le (by positivity)
                (by nlinarith [hsqrt9_ge])
        _ = (125 / 1296 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) := by
              have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
              have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
              have hexp_half_ne : Real.exp (r / 2) ≠ 0 := (Real.exp_pos _).ne'
              field_simp [hrpos.ne', hexp_ne, hexp_half_ne]
              have hexp_half_pow9 :
                  (Real.exp (r / 2)) ^ 9 = Real.exp (9 * (r / 2)) := by
                rw [← Real.exp_nat_mul]
                norm_num
              rw [hexp_half_pow9]
              ring_nf
              rw [bell_exp_pow_three]
              rw [← Real.exp_add]
              ring_nf
        _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
              mul_le_mul_of_nonneg_right (by norm_num : (125 / 1296 : ℝ) ≤ 10)
                (Real.exp_pos _).le
    calc
      ‖Complex.I * ((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
        (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9‖
          = ‖((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
              (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9))‖ * |x| ^ 9 := by
            rw [norm_mul, norm_mul, norm_I, one_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs]
      _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 9 :=
            mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 9)
      _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 9 := by ring

private lemma bell_third_extra10_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (bellSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 10 := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb5_ge : (r ^ 2 * Real.exp r) ^ 5 ≤ (bellSaddleBReal r) ^ 5 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 5
  have hnum_nonneg : 0 ≤ (bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r :=
    mul_nonneg (sq_nonneg _) (bell_b4_nonneg_of_ge_one hr)
  have hnum_le :
      (bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r ≤
        375 * r ^ 10 * (Real.exp r) ^ 3 := by
    have hb3sq :
        (bellSaddleB3Real r) ^ 2 ≤ (5 * r ^ 3 * Real.exp r) ^ 2 :=
      pow_le_pow_left₀ (bell_b3_nonneg_of_ge_one hr) (bell_b3_le hr) 2
    calc
      (bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r
          ≤ (5 * r ^ 3 * Real.exp r) ^ 2 * (15 * r ^ 4 * Real.exp r) :=
            mul_le_mul hb3sq (bell_b4_le hr) (bell_b4_nonneg_of_ge_one hr)
              (by positivity)
      _ = 375 * r ^ 10 * (Real.exp r) ^ 3 := by ring
  have hcoef :
      ‖(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (bellSaddleBReal r : ℂ) ^ 5)))‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
        (1728 * (bellSaddleBReal r : ℂ) ^ 5)))‖
          = ((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r) /
              (1728 * (bellSaddleBReal r) ^ 5) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hnum_nonneg]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_b_norm_eq_of_ge_one hr]
      _ ≤ (375 * r ^ 10 * (Real.exp r) ^ 3) /
              (1728 * (r ^ 2 * Real.exp r) ^ 5) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb5_ge])
      _ = (125 / 576 : ℝ) * Real.exp (-(2 * r)) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hrpos.ne', hexp_ne]
            ring_nf
            rw [Real.exp_neg, sq]
            field_simp [hexp_ne]
            rw [bell_exp_mul_two]
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hr0 : 0 ≤ r := le_trans zero_le_one hr
            calc
              (125 / 576 : ℝ) * Real.exp (-(2 * r))
                  ≤ (125 / 576 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_left
                      (bell_exp_neg_two_le_neg_three_halves hr0) (by norm_num)
              _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  calc
    ‖(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (bellSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)‖
        = ‖(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
            (1728 * (bellSaddleBReal r : ℂ) ^ 5)))‖ * |x| ^ 10 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 10)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 10 := by ring

private lemma bell_third_extra12_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (bellSaddleBReal r : ℂ) ^ 6) * (x : ℂ) ^ 12)‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 12 := by
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := bell_b_ge_rsq_exp hr
  have hb6_ge : (r ^ 2 * Real.exp r) ^ 6 ≤ (bellSaddleBReal r) ^ 6 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 6
  have hnum_le :
      (bellSaddleB3Real r) ^ 4 ≤ 625 * r ^ 12 * (Real.exp r) ^ 4 := by
    calc
      (bellSaddleB3Real r) ^ 4 ≤ (5 * r ^ 3 * Real.exp r) ^ 4 :=
        pow_le_pow_left₀ (bell_b3_nonneg_of_ge_one hr) (bell_b3_le hr) 4
      _ = 625 * r ^ 12 * (Real.exp r) ^ 4 := by ring
  have hcoef :
      ‖((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (bellSaddleBReal r : ℂ) ^ 6))‖ ≤
        10 * Real.exp (-(3 / 2 : ℝ) * r) := by
    calc
      ‖((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
        (31104 * (bellSaddleBReal r : ℂ) ^ 6))‖
          = (bellSaddleB3Real r) ^ 4 / (31104 * (bellSaddleBReal r) ^ 6) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : 0 ≤ (bellSaddleB3Real r) ^ 4)]
            simp only [norm_mul, Complex.norm_ofNat, norm_pow]
            rw [bell_b_norm_eq_of_ge_one hr]
      _ ≤ (625 * r ^ 12 * (Real.exp r) ^ 4) /
              (31104 * (r ^ 2 * Real.exp r) ^ 6) := by
            exact div_le_div₀ (by positivity) hnum_le (by positivity)
              (by nlinarith [hb6_ge])
      _ = (625 / 31104 : ℝ) * Real.exp (-(2 * r)) := by
            have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hrpos.ne', hexp_ne]
            ring_nf
            rw [Real.exp_neg, sq]
            field_simp [hexp_ne]
            rw [bell_exp_mul_two]
      _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) := by
            have hr0 : 0 ≤ r := le_trans zero_le_one hr
            calc
              (625 / 31104 : ℝ) * Real.exp (-(2 * r))
                  ≤ (625 / 31104 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_left
                      (bell_exp_neg_two_le_neg_three_halves hr0) (by norm_num)
              _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) :=
                    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  calc
    ‖((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (bellSaddleBReal r : ℂ) ^ 6) * (x : ℂ) ^ 12)‖
        = ‖((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
            (31104 * (bellSaddleBReal r : ℂ) ^ 6))‖ * |x| ^ 12 := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(3 / 2 : ℝ) * r)) * |x| ^ 12 :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 12)
    _ = 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 12 := by ring

private lemma norm_add8_le (z1 z2 z3 z4 z5 z6 z7 z8 : ℂ) :
    ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ + ‖z7‖ + ‖z8‖ := by
  have h1 : ‖z1 + z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z1‖ + ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z1 (z2 + z3 + z4 + z5 + z6 + z7 + z8)
  have h2 : ‖z2 + z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z2‖ + ‖z3 + z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z2 (z3 + z4 + z5 + z6 + z7 + z8)
  have h3 : ‖z3 + z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z3‖ + ‖z4 + z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z3 (z4 + z5 + z6 + z7 + z8)
  have h4 : ‖z4 + z5 + z6 + z7 + z8‖ ≤
      ‖z4‖ + ‖z5 + z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z4 (z5 + z6 + z7 + z8)
  have h5 : ‖z5 + z6 + z7 + z8‖ ≤ ‖z5‖ + ‖z6 + z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z5 (z6 + z7 + z8)
  have h6 : ‖z6 + z7 + z8‖ ≤ ‖z6‖ + ‖z7 + z8‖ := by
    simpa [add_assoc] using norm_add_le z6 (z7 + z8)
  have h7 : ‖z7 + z8‖ ≤ ‖z7‖ + ‖z8‖ := norm_add_le z7 z8
  nlinarith

private lemma bell_third_extra_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
        bellSaddleB5Real bellSaddleB6Real r x -
      saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x‖
      ≤ 1000 * Real.exp (-(3 / 2 : ℝ) * r) *
        (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
          |x| ^ 9 + |x| ^ 10 + |x| ^ 12) := by
  let T5 : ℂ :=
    Complex.I * ((bellSaddleB5Real r : ℂ) /
      (120 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 5)) * (x : ℂ) ^ 5
  let T6 : ℂ :=
    -((bellSaddleB6Real r : ℂ) / (720 * (bellSaddleBReal r : ℂ) ^ 3)) *
      (x : ℂ) ^ 6
  let T7 : ℂ :=
    -Complex.I * (((bellSaddleB3Real r * bellSaddleB4Real r : ℝ) : ℂ) /
      (144 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 *
        (bellSaddleBReal r : ℂ) ^ 2)) * (x : ℂ) ^ 7
  let T8a : ℂ :=
    (((bellSaddleB3Real r * bellSaddleB5Real r : ℝ) : ℂ) /
      (720 * (bellSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T8b : ℂ :=
    ((((bellSaddleB4Real r) ^ 2 : ℝ) : ℂ) /
      (1152 * (bellSaddleBReal r : ℂ) ^ 4)) * (x : ℂ) ^ 8
  let T9 : ℂ :=
    Complex.I * ((((bellSaddleB3Real r) ^ 3 : ℝ) : ℂ) /
      (1296 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 9)) * (x : ℂ) ^ 9
  let T10 : ℂ :=
    -(((((bellSaddleB3Real r) ^ 2 * bellSaddleB4Real r : ℝ) : ℂ) /
      (1728 * (bellSaddleBReal r : ℂ) ^ 5)) * (x : ℂ) ^ 10)
  let T12 : ℂ :=
    ((((bellSaddleB3Real r) ^ 4 : ℝ) : ℂ) /
      (31104 * (bellSaddleBReal r : ℂ) ^ 6)) * (x : ℂ) ^ 12
  have h5 : ‖T5‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 := by
    dsimp [T5]
    exact bell_third_extra5_norm_le (r := r) (x := x) hr
  have h6 : ‖T6‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 6 := by
    dsimp [T6]
    simpa [norm_neg] using bell_third_extra6_norm_le (r := r) (x := x) hr
  have h7 : ‖T7‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 7 := by
    dsimp [T7]
    simpa [norm_neg] using bell_third_extra7_norm_le (r := r) (x := x) hr
  have h8a : ‖T8a‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by
    dsimp [T8a]
    exact bell_third_extra8a_norm_le (r := r) (x := x) hr
  have h8b : ‖T8b‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 := by
    dsimp [T8b]
    exact bell_third_extra8b_norm_le (r := r) (x := x) hr
  have h9 : ‖T9‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 9 := by
    dsimp [T9]
    exact bell_third_extra9_norm_le (r := r) (x := x) hr
  have h10 : ‖T10‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 10 := by
    dsimp [T10]
    simpa [norm_neg] using bell_third_extra10_norm_le (r := r) (x := x) hr
  have h12 : ‖T12‖ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 12 := by
    dsimp [T12]
    exact bell_third_extra12_norm_le (r := r) (x := x) hr
  have hdiff :
      saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r x -
        saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x =
        T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12 := by
    dsimp [T5, T6, T7, T8a, T8b, T9, T10, T12]
    ring
  have hD_nonneg : 0 ≤ Real.exp (-(3 / 2 : ℝ) * r) := (Real.exp_pos _).le
  have hnonneg : 0 ≤ |x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
      |x| ^ 9 + |x| ^ 10 + |x| ^ 12 := by positivity
  rw [hdiff]
  calc
    ‖T5 + T6 + T7 + T8a + T8b + T9 + T10 + T12‖
        ≤ ‖T5‖ + ‖T6‖ + ‖T7‖ + ‖T8a‖ + ‖T8b‖ + ‖T9‖ + ‖T10‖ + ‖T12‖ :=
          norm_add8_le T5 T6 T7 T8a T8b T9 T10 T12
    _ ≤ 10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 6 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 7 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 8 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 9 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 10 +
          10 * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 12 := by
          nlinarith
    _ ≤ 1000 * Real.exp (-(3 / 2 : ℝ) * r) *
          (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
            |x| ^ 9 + |x| ^ 10 + |x| ^ 12) := by
          nlinarith [hD_nonneg, hnonneg, pow_nonneg (abs_nonneg x) 5,
            pow_nonneg (abs_nonneg x) 6, pow_nonneg (abs_nonneg x) 7,
            pow_nonneg (abs_nonneg x) 8, pow_nonneg (abs_nonneg x) 9,
            pow_nonneg (abs_nonneg x) 10, pow_nonneg (abs_nonneg x) 12]

private lemma bell_local_third_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r))) -
            saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
              bellSaddleB5Real bellSaddleB6Real r x)‖ := by
    unfold bellLocalExponent saddleThirdPoly saddleSecondPoly
    fun_prop
  simpa [bell_saddleLocalRatio_eq] using h

private lemma bell_local_second_integrand_continuous_for_third (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ := by
  have h :
      Continuous fun x : ℝ =>
        ‖Complex.exp (-(x ^ 2) / 2) *
          (Complex.exp (bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r))) -
            saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ := by
    unfold bellLocalExponent saddleSecondPoly
    fun_prop
  simpa [bell_saddleLocalRatio_eq] using h

private lemma bell_third_extra_integrand_continuous (r : ℝ) :
    Continuous fun x : ℝ =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r x -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ := by
  unfold saddleThirdPoly saddleSecondPoly
  fun_prop

private lemma bell_local_third_extra_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
          (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
              bellSaddleB5Real bellSaddleB6Real r x -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
          bellSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, bellThirdGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact bellThirdGaussianDom_integral_nonneg
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ =>
          8000 * M * Real.exp (-(1 / 2 : ℝ) * r))
        atTop (𝓝 0) := by
    have hlin : Tendsto (fun r : ℝ => (-(1 / 2 : ℝ)) * r) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0) tendsto_id
    have hexp : Tendsto (fun r : ℝ => Real.exp ((-(1 / 2 : ℝ)) * r)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hlin
    simpa [mul_assoc] using hexp.const_mul (8000 * M)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℝ), bellSecondCorrScale_pos_eventually] with
      r hr hcorr
    let L : ℝ := bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, bellSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
              bellSaddleB5Real bellSaddleB6Real r x -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), bellSecondCorrScale_lower_exp_eventually,
      bellSecondCorrScale_pos_eventually] with r hr hcorrLower hcorrPos
    let L : ℝ := bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r x -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖
    let G : ℝ → ℝ := fun x =>
      (1000 * Real.exp (-(3 / 2 : ℝ) * r)) * bellThirdGaussianDom x
    have hLnonneg : 0 ≤ L := by
      dsimp [L, bellSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ G x := by
      intro x hx
      have hdiff := bell_third_extra_norm_le (r := r) (x := x) hr
      dsimp [F, G, bellThirdGaussianDom]
      rw [norm_mul]
      have hgauss :
          ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
        rw [Complex.norm_exp]
        congr 1
        simp [pow_two]
      rw [hgauss]
      calc
        Real.exp (-(x ^ 2) / 2) *
            ‖saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
                bellSaddleB5Real bellSaddleB6Real r x -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x‖
            ≤ Real.exp (-(x ^ 2) / 2) *
                (1000 * Real.exp (-(3 / 2 : ℝ) * r) *
                  (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                    |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) :=
              mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
        _ = 1000 * Real.exp (-(3 / 2 : ℝ) * r) *
            (Real.exp (-(x ^ 2) / 2) *
              (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 +
                |x| ^ 9 + |x| ^ 10 + |x| ^ 12)) := by ring
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (bell_third_extra_integrand_continuous r).intervalIntegrable _ _
    have hGint : IntervalIntegrable G volume (-L) L := by
      exact (bellThirdGaussianDom_continuous.const_mul
        (1000 * Real.exp (-(3 / 2 : ℝ) * r))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M := by
      have hconst_nonneg :
          0 ≤ 1000 * Real.exp (-(3 / 2 : ℝ) * r) := by positivity
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, G x :=
          intervalIntegral.integral_mono_on hle hFint hGint hpoint
        _ = (1000 * Real.exp (-(3 / 2 : ℝ) * r)) *
              (∫ x in -L..L, bellThirdGaussianDom x) := by
          dsimp [G]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact bellThirdGaussianDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hnum_nonneg :
        0 ≤ (1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M := by positivity
    have hscale_pos : 0 < (1 / 8 : ℝ) * Real.exp (-r) := by positivity
    have hmain :
        (∫ x in -L..L, F x) / bellSecondCorrScale r ≤
          ((1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
            ((1 / 8 : ℝ) * Real.exp (-r)) := by
      calc
        (∫ x in -L..L, F x) / bellSecondCorrScale r
            ≤ ((1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
                bellSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
              ((1 / 8 : ℝ) * Real.exp (-r)) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
          (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
              bellSaddleB5Real bellSaddleB6Real r x -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
          bellSecondCorrScale r)
          = (∫ x in -L..L, F x) / bellSecondCorrScale r := by rfl
      _ ≤ ((1000 * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
            ((1 / 8 : ℝ) * Real.exp (-r)) := hmain
      _ = 8000 * M * Real.exp (-(1 / 2 : ℝ) * r) := by
        have hexp_ne : Real.exp (-r) ≠ 0 := (Real.exp_pos (-r)).ne'
        field_simp [hexp_ne]
        have hexp_calc' :
            Real.exp (-(3 / 2 : ℝ) * r) =
              Real.exp (-(1 / 2 : ℝ) * r) * Real.exp (-r) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (-(3 * r / 2)) = Real.exp (-(3 / 2 : ℝ) * r) by
          congr 1
          ring]
        rw [hexp_calc']
        ring

theorem bell_local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
          (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
                bellSaddleB5Real bellSaddleB6Real r x)‖) /
          bellThirdCorrScale r)
      atTop (𝓝 0) := by
  unfold bellThirdCorrScale
  let T : ℝ → ℝ := fun r =>
    (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
      (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real r x)‖) / bellSecondCorrScale r
  let S : ℝ → ℝ := fun r =>
    (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
      (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
      bellSecondCorrScale r
  let E : ℝ → ℝ := fun r =>
    (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
      (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r x -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
      bellSecondCorrScale r
  change Tendsto T atTop (𝓝 0)
  have hsecond := bell_local_second_L1
  have hextra := bell_local_third_extra_L1
  have hsum : Tendsto (fun r : ℝ => S r + E r) atTop (𝓝 0) := by
    simpa [S, E] using hsecond.add hextra
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [bellSecondCorrScale_pos_eventually] with r hcorr
    let L : ℝ := bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)
    have hLnonneg : 0 ≤ L := by
      dsimp [L, bellSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hint_nonneg :
        0 ≤ ∫ x in -L..L,
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
                bellSaddleB5Real bellSaddleB6Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    dsimp [T]
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [bellSecondCorrScale_pos_eventually] with r hcorr
    let L : ℝ := bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)
    let FT : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real r x)‖
    let FS : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖
    let FE : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          bellSaddleB5Real bellSaddleB6Real r x -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖
    have hLnonneg : 0 ≤ L := by
      dsimp [L, bellSaddleDeltaReal]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, FT x ≤ FS x + FE x := by
      intro x hx
      dsimp [FT, FS, FE]
      calc
        ‖Complex.exp (-(x ^ 2) / 2) *
          (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
              bellSaddleAReal bellSaddleBReal r
              (x / Real.sqrt (bellSaddleBReal r)) -
            saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
              bellSaddleB5Real bellSaddleB6Real r x)‖
            =
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x) -
            Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
                bellSaddleB5Real bellSaddleB6Real r x -
                saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ := by
              congr 1
              ring
        _ ≤
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ +
          ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleThirdPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
                bellSaddleB5Real bellSaddleB6Real r x -
                saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ :=
            norm_sub_le _ _
    have hFTint : IntervalIntegrable FT volume (-L) L := by
      exact (bell_local_third_integrand_continuous r).intervalIntegrable _ _
    have hFSint : IntervalIntegrable FS volume (-L) L := by
      exact (bell_local_second_integrand_continuous_for_third r).intervalIntegrable _ _
    have hFEint : IntervalIntegrable FE volume (-L) L := by
      exact (bell_third_extra_integrand_continuous r).intervalIntegrable _ _
    have hsumInt : IntervalIntegrable (fun x : ℝ => FS x + FE x) volume (-L) L :=
      hFSint.add hFEint
    have hInt :
        (∫ x in -L..L, FT x) ≤ (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
      calc
        (∫ x in -L..L, FT x) ≤ ∫ x in -L..L, FS x + FE x :=
          intervalIntegral.integral_mono_on hle hFTint hsumInt hpoint
        _ = (∫ x in -L..L, FS x) + (∫ x in -L..L, FE x) := by
          rw [intervalIntegral.integral_add hFSint hFEint]
    have hdiv :
        (∫ x in -L..L, FT x) / bellSecondCorrScale r ≤
          ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            bellSecondCorrScale r :=
      div_le_div_of_nonneg_right hInt hcorr.le
    calc
      T r = (∫ x in -L..L, FT x) / bellSecondCorrScale r := by rfl
      _ ≤ ((∫ x in -L..L, FS x) + (∫ x in -L..L, FE x)) /
            bellSecondCorrScale r := hdiv
      _ = S r + E r := by
        dsimp [S, E, FS, FE, L]
        ring

def bellThirdOrderHAdmissible :
    ThirdOrderHAdmissible bellHAdmissible bellSecondOrderHAdmissible where
  b5 := bellSaddleB5Real
  b6 := bellSaddleB6Real
  corrScale3 := bellThirdCorrScale
  corrScale3_pos := by
    simpa [bellHAdmissible, bellThirdCorrScale] using bellSecondCorrScale_pos_eventually
  corrScale3_tendsto_zero := by
    simpa [bellHAdmissible, bellThirdCorrScale] using bellSecondCorrScale_tendsto_zero
  corrScale3_dominates_correction := by
    simpa [bellHAdmissible, bellThirdCorrScale, bellSecondOrderHAdmissible] using
      bell_saddleThirdCorrectionScale_le_second
  local_third_L1 := by
    simpa [bellHAdmissible, bellThirdCorrScale, bellSecondOrderHAdmissible] using
      bell_local_third_L1
  tail_third_uniform := by
    simpa [bellHAdmissible, bellThirdCorrScale] using bell_tail_second_uniform


