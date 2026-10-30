-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellSecondOrder
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_BellSecondOrder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:24:31.785688+00:00
-- url     : https://prove2.me/theorems/bbccd8f5-52fb-477d-b4bc-8a2b8c252729
-- title:
--   Bell first correction and robust error functions
-- statement:
--   The third and fourth logarithmic saddle functions are the stated Touchard polynomials times exp(r). The scale c2=|b4|/b²+b3²/b³, the actual complex saddle denominator, and first correction define explicit series/number error functions. Local Taylor remainders, scaled cubic/quartic terms, Gaussian polynomial dominators and tail bounds supply a second-order record.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/BellSecondOrder.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
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
# Second-order saddle data for Bell numbers

This file adds the second-order correction layer for
`exp (exp z - 1)`.  The logarithmic saddle derivatives are
`b₃(r) = (r + 3r² + r³)e^r` and
`b₄(r) = (r + 7r² + 6r³ + r⁴)e^r`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 800000

noncomputable section

/-- Third logarithmic saddle derivative for Bell numbers. -/
def bellSaddleB3Real (r : ℝ) : ℝ :=
  (r + 3 * r ^ 2 + r ^ 3) * Real.exp r

/-- Fourth logarithmic saddle derivative for Bell numbers. -/
def bellSaddleB4Real (r : ℝ) : ℝ :=
  (r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4) * Real.exp r

/-- Robust second-order correction scale for Bell numbers. -/
def bellSecondCorrScale (r : ℝ) : ℝ :=
  saddleCorrectionScale bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r

/-- Complex saddle scale used by the Bell second-order statement. -/
def bellSecondOrderSaddleScale (n : ℕ) : ℂ :=
  saddleScale (fun z : ℂ => Complex.exp (Complex.exp z - 1))
    bellSaddleRadius (fun n => bellSaddleBReal (bellSaddleRadius n)) n

/-- The explicit Bell second-order correction at the saddle radius. -/
def bellSecondCorrectionAtSaddle (n : ℕ) : ℝ :=
  saddleCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
    (bellSaddleRadius n)

/-- Error term for the formal Bell EGF coefficient. -/
def bellSecondOrderSeriesError (n : ℕ) : ℂ :=
  bellSeries.coeff n / bellSecondOrderSaddleScale n -
    (1 + (bellSecondCorrectionAtSaddle n : ℂ))

/-- Error term for `B_n / n!`. -/
def bellSecondOrderNumberError (n : ℕ) : ℂ :=
  (((AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) /
      n.factorial : ℝ) : ℂ) /
    bellSecondOrderSaddleScale n -
    (1 + (bellSecondCorrectionAtSaddle n : ℂ))

lemma bellSecondCorrScale_eq_formula {r : ℝ} (hr : 0 < r) :
    bellSecondCorrScale r =
      Real.exp (-r) *
        (2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
          (r * (r + 1) ^ 3) := by
  unfold bellSecondCorrScale saddleCorrectionScale bellSaddleBReal bellSaddleB3Real
    bellSaddleB4Real
  have hb4_nonneg : 0 ≤ (r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4) * Real.exp r := by
    positivity
  rw [abs_of_nonneg hb4_nonneg]
  rw [Real.exp_neg]
  have her : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have hrn : r ≠ 0 := hr.ne'
  have hr1 : r + 1 ≠ 0 := by positivity
  field_simp [hrn, her, hr1]
  ring

lemma bellSecondCorrScale_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < bellSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  unfold bellSecondCorrScale saddleCorrectionScale bellSaddleBReal bellSaddleB3Real
    bellSaddleB4Real
  have hbpos : 0 < r * (r + 1) * Real.exp r := by positivity
  have hb4pos : 0 < (r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4) * Real.exp r := by
    positivity
  have hfirst :
      0 < |(r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4) * Real.exp r| /
          (r * (r + 1) * Real.exp r) ^ 2 :=
    div_pos (abs_pos.mpr hb4pos.ne') (sq_pos_of_pos hbpos)
  have hsecond :
      0 ≤ ((r + 3 * r ^ 2 + r ^ 3) * Real.exp r) ^ 2 /
          (r * (r + 1) * Real.exp r) ^ 3 := by
    positivity
  exact add_pos_of_pos_of_nonneg hfirst hsecond

lemma bellSecondCorrScale_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ bellSecondCorrScale r :=
  bellSecondCorrScale_pos_eventually.mono fun _ h => h.le

lemma bellSecondCorrScale_lower_exp_eventually :
    ∀ᶠ r : ℝ in atTop,
      (1 / 8 : ℝ) * Real.exp (-r) ≤ bellSecondCorrScale r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [bellSecondCorrScale_eq_formula hrpos]
  have hdenpos : 0 < r * (r + 1) ^ 3 := by positivity
  have hpoly :
      (1 / 8 : ℝ) ≤
        (2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
          (r * (r + 1) ^ 3) := by
    field_simp [hdenpos.ne']
    ring_nf
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
      show 0 ≤ r ^ 4 by positivity]
  calc
    (1 / 8 : ℝ) * Real.exp (-r)
        ≤ ((2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
            (r * (r + 1) ^ 3)) * Real.exp (-r) :=
          mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = Real.exp (-r) *
        (2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
          (r * (r + 1) ^ 3) := by ring

lemma bellSecondCorrScale_le_exp_eventually :
    ∀ᶠ r : ℝ in atTop, bellSecondCorrScale r ≤ 100 * Real.exp (-r) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [bellSecondCorrScale_eq_formula hrpos]
  have hdenpos : 0 < r * (r + 1) ^ 3 := by positivity
  have hpoly :
      (2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
          (r * (r + 1) ^ 3) ≤ 100 := by
    field_simp [hdenpos.ne']
    ring_nf
    nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
      show 0 ≤ r ^ 4 by positivity]
  calc
    Real.exp (-r) *
        (2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
          (r * (r + 1) ^ 3)
        = Real.exp (-r) *
            ((2 * r ^ 4 + 13 * r ^ 3 + 24 * r ^ 2 + 14 * r + 2) /
              (r * (r + 1) ^ 3)) := by ring
    _ ≤ Real.exp (-r) * 100 :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = 100 * Real.exp (-r) := by ring

lemma bellSecondCorrScale_tendsto_zero :
    Tendsto bellSecondCorrScale atTop (𝓝 0) := by
  have hneg : Tendsto (fun r : ℝ => (-1 : ℝ) * r) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by norm_num : (-1 : ℝ) < 0) tendsto_id
  have hexp : Tendsto (fun r : ℝ => Real.exp ((-1 : ℝ) * r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hupper : Tendsto (fun r : ℝ => 100 * Real.exp (-r)) atTop (𝓝 0) := by
    have hmul :
        Tendsto (fun r : ℝ => 100 * Real.exp ((-1 : ℝ) * r)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hexp.const_mul (100 : ℝ)
    refine Tendsto.congr' ?_ hmul
    exact Eventually.of_forall fun r => by
      ring_nf
  exact squeeze_zero' bellSecondCorrScale_nonneg_eventually
    bellSecondCorrScale_le_exp_eventually hupper

/-- A stronger Bell tail envelope, small enough for the second-order scale. -/
def bellSecondTailE (r : ℝ) : ℝ :=
  Real.exp (-((1 / Real.pi ^ 2 : ℝ) * r * Real.exp ((1 / 5 : ℝ) * r)))

lemma bellSecondTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ bellSecondTailE r :=
  Eventually.of_forall fun r => by
    unfold bellSecondTailE
    positivity

lemma bell_second_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      bellSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖ ≤
          bellSecondTailE r := by
  set_option backward.isDefEq.respectTransparency false in
    let c : ℝ := 2 / Real.pi ^ 2
    have hcpos : 0 < c := by
      dsimp [c]
      positivity
    have hy_small :
        ∀ᶠ r : ℝ in atTop,
          c * (r * (bellSaddleDeltaReal r) ^ 2) ≤ 1 / 2 := by
      simpa [c] using bell_tail_y_tendsto_zero.eventually_le_const
        (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hy_small] with
      r hr hy_small_r n θ hδθ hθπ
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hδpos : 0 ≤ bellSaddleDeltaReal r := by
      unfold bellSaddleDeltaReal
      positivity
    have hθsq_ge : (bellSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (bellSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδpos hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    let y : ℝ := c * (r * (bellSaddleDeltaReal r) ^ 2)
    have hy0 : 0 ≤ y := by
      dsimp [y, c]
      positivity
    have hyhalf : y ≤ 1 / 2 := by
      simpa [y, c] using hy_small_r
    have hone_sub : y / 2 ≤ 1 - Real.exp (-y) :=
      bell_one_sub_exp_neg_ge_half hy0 hyhalf
    have hcos := Real.cos_le_one_sub_mul_cos_sq hθπ
    have hrcos_le : r * Real.cos θ ≤ r - c * (r * (bellSaddleDeltaReal r) ^ 2) := by
      have hcos' : Real.cos θ ≤ 1 - c * θ ^ 2 := by
        dsimp [c] at hcos ⊢
        linarith
      have hmul := mul_le_mul_of_nonneg_left hcos' hr0
      have hsquare : c * (r * (bellSaddleDeltaReal r) ^ 2) ≤ c * (r * θ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθsq_ge hr0) hcpos.le
      calc
        r * Real.cos θ ≤ r * (1 - c * θ ^ 2) := hmul
        _ = r - c * (r * θ ^ 2) := by ring_nf
        _ ≤ r - c * (r * (bellSaddleDeltaReal r) ^ 2) := by linarith
    have hexp_rcos_le : Real.exp (r * Real.cos θ) ≤ Real.exp r * Real.exp (-y) := by
      have harg : r * Real.cos θ ≤ r - y := by
        simpa [y] using hrcos_le
      calc
        Real.exp (r * Real.cos θ) ≤ Real.exp (r - y) := Real.exp_le_exp.mpr harg
        _ = Real.exp r * Real.exp (-y) := by
          rw [show r - y = r + -y by ring_nf, Real.exp_add]
    have hdiff :
        Real.exp (r * Real.cos θ) - Real.exp r ≤
          -Real.exp r * (1 - Real.exp (-y)) := by
      calc
        Real.exp (r * Real.cos θ) - Real.exp r
            ≤ Real.exp r * Real.exp (-y) - Real.exp r :=
              sub_le_sub_right hexp_rcos_le _
        _ = -Real.exp r * (1 - Real.exp (-y)) := by ring_nf
    have hstrong :
        Real.exp (r * Real.cos θ) - Real.exp r ≤
          -((1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r)) := by
      have hmul : Real.exp r * (y / 2) ≤ Real.exp r * (1 - Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left hone_sub (Real.exp_pos r).le
      have hneg :
          -Real.exp r * (1 - Real.exp (-y)) ≤ -Real.exp r * (y / 2) := by
        nlinarith
      calc
        Real.exp (r * Real.cos θ) - Real.exp r
            ≤ -Real.exp r * (1 - Real.exp (-y)) := hdiff
        _ ≤ -Real.exp r * (y / 2) := hneg
        _ = -((1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r)) := by
          dsimp [y, c, bellSaddleDeltaReal]
          rw [show (Real.exp (-(2 / 5 : ℝ) * r)) ^ 2 =
              Real.exp (2 * (-(2 / 5 : ℝ) * r)) by
                rw [← Real.exp_nat_mul]
                norm_num]
          calc
            -Real.exp r * (2 / Real.pi ^ 2 * (r * Real.exp (2 * (-(2 / 5 : ℝ) * r))) / 2)
                = -(1 / Real.pi ^ 2 * r *
                      (Real.exp r * Real.exp (2 * (-(2 / 5 : ℝ) * r)))) := by ring_nf
            _ = -(1 / Real.pi ^ 2 * r *
                      Real.exp (r + 2 * (-(2 / 5 : ℝ) * r))) := by
                  rw [← Real.exp_add]
            _ = -((1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r)) := by
                  ring_nf
    calc
      ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖
          ≤ Real.exp (Real.exp (r * Real.cos θ) - Real.exp r) :=
            bell_saddleGAt_norm_le_exp r n θ
      _ ≤ Real.exp (-((1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r))) :=
            Real.exp_le_exp.mpr hstrong
      _ = bellSecondTailE r := by rfl

lemma bellSecondTailE_decay :
    Tendsto
      (fun r : ℝ =>
        Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellSecondTailE r /
          bellSecondCorrScale r)
      atTop (𝓝 0) := by
  have hcoef_top :
      Tendsto (fun r : ℝ => (1 / Real.pi ^ 2 : ℝ) *
        Real.exp ((1 / 5 : ℝ) * r)) atTop atTop := by
    exact Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 1 / Real.pi ^ 2)
      bell_exp_one_fifth_tendsto_atTop
  have hcoef_big :
      ∀ᶠ r : ℝ in atTop,
        3 ≤ (1 / Real.pi ^ 2 : ℝ) * Real.exp ((1 / 5 : ℝ) * r) :=
    hcoef_top.eventually_ge_atTop 3
  have hbase :
      Tendsto (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (3 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 3 / 2)
  have hupper :
      Tendsto (fun r : ℝ =>
        (8 * Real.sqrt (4 * Real.pi)) *
          (r * Real.exp (-(3 / 2 : ℝ) * r))) atTop (𝓝 0) := by
    have hcongr :
        (fun r : ℝ => r * Real.exp (-(3 / 2 : ℝ) * r)) =ᶠ[atTop]
          fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(3 / 2 : ℝ) * r) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      rw [Real.rpow_one]
    simpa using
      ((Tendsto.congr' hcongr.symm hbase).const_mul
        (8 * Real.sqrt (4 * Real.pi)))
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [bellSecondCorrScale_pos_eventually] with r hcorr
    exact div_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (by unfold bellSecondTailE; positivity)) hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), bellSecondCorrScale_lower_exp_eventually,
      bellSecondCorrScale_pos_eventually, hcoef_big] with r hr hcorrLower hcorrPos hcoef
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hαpos : 0 < (1 / 8 : ℝ) * Real.exp (-r) := by positivity
    have hE_nonneg : 0 ≤ bellSecondTailE r := by
      unfold bellSecondTailE
      positivity
    have hE_le : bellSecondTailE r ≤ Real.exp (-(3 * r)) := by
      unfold bellSecondTailE
      have hmul :
          3 * r ≤ (1 / Real.pi ^ 2 : ℝ) * r * Real.exp ((1 / 5 : ℝ) * r) := by
        calc
          3 * r ≤ ((1 / Real.pi ^ 2 : ℝ) * Real.exp ((1 / 5 : ℝ) * r)) * r :=
            mul_le_mul_of_nonneg_right hcoef hr0
          _ = (1 / Real.pi ^ 2 : ℝ) * r * Real.exp ((1 / 5 : ℝ) * r) := by
            ring
      exact Real.exp_le_exp.mpr (neg_le_neg hmul)
    have hB_le : 2 * Real.pi * bellSaddleBReal r ≤
        4 * Real.pi * (r ^ 2 * Real.exp r) := by
      have hrp1 : r + 1 ≤ 2 * r := by linarith
      have hmul : r * (r + 1) ≤ r * (2 * r) :=
        mul_le_mul_of_nonneg_left hrp1 hr0
      have hB : bellSaddleBReal r ≤ 2 * r ^ 2 * Real.exp r := by
        unfold bellSaddleBReal
        calc
          r * (r + 1) * Real.exp r ≤ r * (2 * r) * Real.exp r :=
            mul_le_mul_of_nonneg_right hmul (Real.exp_pos r).le
          _ = 2 * r ^ 2 * Real.exp r := by ring_nf
      calc
        2 * Real.pi * bellSaddleBReal r
            ≤ 2 * Real.pi * (2 * r ^ 2 * Real.exp r) :=
              mul_le_mul_of_nonneg_left hB (by positivity)
        _ = 4 * Real.pi * (r ^ 2 * Real.exp r) := by ring_nf
    have hsqrt :
        Real.sqrt (2 * Real.pi * bellSaddleBReal r) ≤
          Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2)) := by
      calc
        Real.sqrt (2 * Real.pi * bellSaddleBReal r)
            ≤ Real.sqrt (4 * Real.pi * (r ^ 2 * Real.exp r)) :=
              Real.sqrt_le_sqrt hB_le
        _ = Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2)) := by
          have h4pi : 0 ≤ 4 * Real.pi := by positivity
          rw [Real.sqrt_mul h4pi (r ^ 2 * Real.exp r)]
          rw [Real.sqrt_mul (sq_nonneg r) (Real.exp r)]
          rw [Real.sqrt_sq hr0]
          rw [← Real.exp_half]
    have hnum :
        Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellSecondTailE r ≤
          Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2)) * Real.exp (-(3 * r)) := by
      calc
        Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellSecondTailE r
            ≤ (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2))) *
                bellSecondTailE r :=
              mul_le_mul_of_nonneg_right hsqrt hE_nonneg
        _ ≤ (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2))) *
                Real.exp (-(3 * r)) :=
              mul_le_mul_of_nonneg_left hE_le (by positivity)
    calc
      Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellSecondTailE r /
          bellSecondCorrScale r
          ≤ Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellSecondTailE r /
              ((1 / 8 : ℝ) * Real.exp (-r)) :=
            div_le_div_of_nonneg_left
              (mul_nonneg (Real.sqrt_nonneg _) hE_nonneg) hαpos hcorrLower
      _ ≤ (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2)) *
              Real.exp (-(3 * r))) / ((1 / 8 : ℝ) * Real.exp (-r)) :=
            div_le_div_of_nonneg_right hnum hαpos.le
      _ = 8 * Real.sqrt (4 * Real.pi) *
            (r * Real.exp (-(3 / 2 : ℝ) * r)) := by
          have hexp_ne : Real.exp (-r) ≠ 0 := (Real.exp_pos (-r)).ne'
          have hexp_calc :
              Real.exp (r / 2) * Real.exp (-(3 * r)) / Real.exp (-r) =
                Real.exp (-(3 / 2 : ℝ) * r) := by
            rw [← Real.exp_add]
            rw [← Real.exp_sub]
            congr 1
            ring
          calc
            (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2)) *
                Real.exp (-(3 * r))) / ((1 / 8 : ℝ) * Real.exp (-r))
                = 8 * Real.sqrt (4 * Real.pi) *
                    (r * (Real.exp (r / 2) * Real.exp (-(3 * r)) /
                      Real.exp (-r))) := by
                  field_simp [hexp_ne]
            _ = 8 * Real.sqrt (4 * Real.pi) *
                    (r * Real.exp (-(3 / 2 : ℝ) * r)) := by
                  rw [hexp_calc]

lemma bell_tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in atTop, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * bellSaddleBReal r) * E r /
          bellSecondCorrScale r)
        atTop (𝓝 0) ∧
      (∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        bellSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖ ≤ E r) := by
  exact ⟨bellSecondTailE, bellSecondTailE_nonneg_eventually, bellSecondTailE_decay,
    bell_second_tail_bound_eventually⟩

private def expLocalRemainderFifth (θ : ℝ) : ℂ :=
  ExpStirling.expLocalRemainder θ -
    ((((θ : ℂ) * Complex.I) ^ 3) / (((3 : ℕ).factorial : ℕ) : ℂ) +
      (((θ : ℂ) * Complex.I) ^ 4) / (((4 : ℕ).factorial : ℕ) : ℂ))

private lemma expLocalRemainderFifth_norm_le {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖expLocalRemainderFifth θ‖ ≤ Real.exp 2 * |θ| ^ 5 := by
  let u : ℂ := (θ : ℂ) * Complex.I
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp u 5
  have hnorm : ‖u‖ = |θ| := by simp [u]
  have hleft :
      ExpStirling.expLocalRemainder θ -
          (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
            u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ)) =
        Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ) := by
    simp [ExpStirling.expLocalRemainder, u, Finset.sum_range_succ]
    ring
  change
    ‖ExpStirling.expLocalRemainder θ -
        (u ^ 3 / (((3 : ℕ).factorial : ℕ) : ℂ) +
          u ^ 4 / (((4 : ℕ).factorial : ℕ) : ℂ))‖ ≤
      Real.exp 2 * |θ| ^ 5
  rw [hleft]
  calc
    ‖Complex.exp u - ∑ m ∈ Finset.range 5, u ^ m / (m.factorial : ℂ)‖
        ≤ ‖u‖ ^ 5 * Real.exp ‖u‖ := htail
    _ = |θ| ^ 5 * Real.exp |θ| := by rw [hnorm]
    _ ≤ |θ| ^ 5 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 5)
    _ = Real.exp 2 * |θ| ^ 5 := by ring

private lemma bellSaddleBReal_pos_of_ge_one {r : ℝ} (hr : 1 ≤ r) :
    0 < bellSaddleBReal r := by
  unfold bellSaddleBReal
  positivity

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

private lemma bell_sqrtB_sq {r : ℝ} (hb : 0 < bellSaddleBReal r) :
    ((Real.sqrt (bellSaddleBReal r) : ℂ) ^ 2) =
      (bellSaddleBReal r : ℂ) := by
  exact_mod_cast (Real.sq_sqrt hb.le)

private def bellScaledCubic (r x : ℝ) : ℂ :=
  -Complex.I *
    ((bellSaddleB3Real r : ℂ) /
      (6 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3)) * (x : ℂ) ^ 3

private def bellScaledQuartic (r x : ℝ) : ℂ :=
  ((bellSaddleB4Real r : ℂ) / (24 * (bellSaddleBReal r : ℂ) ^ 2)) *
    (x : ℂ) ^ 4

private def bellScaledRemainder (r x : ℝ) : ℂ :=
  bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r)) -
    bellScaledCubic r x - bellScaledQuartic r x

private lemma bellLocalExponent_scaled_split (r x : ℝ) :
    bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r)) =
      bellScaledCubic r x + bellScaledQuartic r x + bellScaledRemainder r x := by
  unfold bellScaledRemainder
  ring

private lemma bell_saddleSecondPoly_eq_scaled_terms {r x : ℝ}
    (hb : 0 < bellSaddleBReal r) :
    saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x =
      1 + bellScaledCubic r x + bellScaledQuartic r x +
        (bellScaledCubic r x) ^ 2 / 2 := by
  have hsqrt_sq := bell_sqrtB_sq hb
  have hsqrt_ne : (Real.sqrt (bellSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (bellSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_pow6 :
      (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 6 =
        (bellSaddleBReal r : ℂ) ^ 3 := by
    calc
      (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 6 =
          ((Real.sqrt (bellSaddleBReal r) : ℂ) ^ 2) ^ 3 := by ring
      _ = (bellSaddleBReal r : ℂ) ^ 3 := by rw [hsqrt_sq]
  unfold saddleSecondPoly bellScaledCubic bellScaledQuartic
  field_simp [hsqrt_ne, hb_ne]
  ring_nf
  rw [hsqrt_pow6, Complex.I_sq]
  norm_num [Complex.ofReal_pow]
  ring

private lemma bellScaledCubic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖bellScaledCubic r x‖ ≤ 10 * Real.exp (-(r / 2)) * |x| ^ 3 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (bellSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) :=
    bell_sqrtB_ge_r_exp_half hr
  have hsqrt3_ge :
      (r * Real.exp (r / 2)) ^ 3 ≤ (Real.sqrt (bellSaddleBReal r)) ^ 3 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r * Real.exp (r / 2)) hsqrt_ge 3
  have hb3_nonneg : 0 ≤ bellSaddleB3Real r := by
    unfold bellSaddleB3Real
    positivity
  have hb3_le : bellSaddleB3Real r ≤ 5 * r ^ 3 * Real.exp r := by
    unfold bellSaddleB3Real
    have hpoly : r + 3 * r ^ 2 + r ^ 3 ≤ 5 * r ^ 3 := by
      nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity]
    exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le
  have hcoef :
      ‖(bellSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3)‖ ≤
        10 * Real.exp (-(r / 2)) := by
    calc
      ‖(bellSaddleB3Real r : ℂ) /
          (6 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3)‖
          = bellSaddleB3Real r /
              (6 * (Real.sqrt (bellSaddleBReal r)) ^ 3) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb3_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hsqrt_pos]
      _ ≤ (5 * r ^ 3 * Real.exp r) /
              (6 * (r * Real.exp (r / 2)) ^ 3) := by
            exact div_le_div₀ (by positivity) hb3_le (by positivity)
              (by nlinarith [hsqrt3_ge])
      _ = (5 / 6 : ℝ) * Real.exp (-(r / 2)) := by
            have hr_ne : r ≠ 0 := hrpos.ne'
            field_simp [hr_ne, (Real.exp_pos (r / 2)).ne']
            have hexp_pow3 :
                (Real.exp (r / 2)) ^ 3 = Real.exp (3 * (r / 2)) := by
              rw [← Real.exp_nat_mul]
              norm_num
            rw [hexp_pow3, ← Real.exp_add]
            congr 1
            ring
      _ ≤ 10 * Real.exp (-(r / 2)) := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (5 / 6 : ℝ) ≤ 10)
              (Real.exp_pos _).le
  calc
    ‖bellScaledCubic r x‖
        = ‖(bellSaddleB3Real r : ℂ) /
            (6 * (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3)‖ * |x| ^ 3 := by
          unfold bellScaledCubic
          rw [norm_mul, norm_mul, norm_neg, norm_I, one_mul, norm_pow,
            Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-(r / 2))) * |x| ^ 3 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 3)
    _ = 10 * Real.exp (-(r / 2)) * |x| ^ 3 := by ring

private lemma bellScaledQuartic_norm_le {r x : ℝ} (hr : 1 ≤ r) :
    ‖bellScaledQuartic r x‖ ≤ 10 * Real.exp (-r) * |x| ^ 4 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  have hb_ge : r ^ 2 * Real.exp r ≤ bellSaddleBReal r := by
    unfold bellSaddleBReal
    have hpoly : r ^ 2 ≤ r * (r + 1) := by nlinarith [hr, sq_nonneg r]
    exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le
  have hb_sq_ge : (r ^ 2 * Real.exp r) ^ 2 ≤ (bellSaddleBReal r) ^ 2 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ r ^ 2 * Real.exp r) hb_ge 2
  have hb4_nonneg : 0 ≤ bellSaddleB4Real r := by
    unfold bellSaddleB4Real
    positivity
  have hb4_le : bellSaddleB4Real r ≤ 15 * r ^ 4 * Real.exp r := by
    unfold bellSaddleB4Real
    have hpoly : r + 7 * r ^ 2 + 6 * r ^ 3 + r ^ 4 ≤ 15 * r ^ 4 := by
      nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity,
        show 0 ≤ r ^ 4 by positivity]
    exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos r).le
  have hcoef :
      ‖(bellSaddleB4Real r : ℂ) / (24 * (bellSaddleBReal r : ℂ) ^ 2)‖ ≤
        10 * Real.exp (-r) := by
    calc
      ‖(bellSaddleB4Real r : ℂ) / (24 * (bellSaddleBReal r : ℂ) ^ 2)‖
          = bellSaddleB4Real r / (24 * (bellSaddleBReal r) ^ 2) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hb4_nonneg]
            simp only [norm_mul, norm_ofNat, norm_pow, Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_pos hbpos]
      _ ≤ (15 * r ^ 4 * Real.exp r) /
              (24 * (r ^ 2 * Real.exp r) ^ 2) := by
            exact div_le_div₀ (by positivity) hb4_le (by positivity)
              (by nlinarith [hb_sq_ge])
      _ = (15 / 24 : ℝ) * Real.exp (-r) := by
            have hr_ne : r ≠ 0 := hrpos.ne'
            have hexp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
            field_simp [hr_ne, hexp_ne]
            ring_nf
            rw [Real.exp_neg]
            rw [mul_inv_cancel₀ hexp_ne]
      _ ≤ 10 * Real.exp (-r) := by
            exact mul_le_mul_of_nonneg_right (by norm_num : (15 / 24 : ℝ) ≤ 10)
              (Real.exp_pos _).le
  calc
    ‖bellScaledQuartic r x‖
        = ‖(bellSaddleB4Real r : ℂ) /
            (24 * (bellSaddleBReal r : ℂ) ^ 2)‖ * |x| ^ 4 := by
          unfold bellScaledQuartic
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (10 * Real.exp (-r)) * |x| ^ 4 :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg x) 4)
    _ = 10 * Real.exp (-r) * |x| ^ 4 := by ring

private def complexExpRemainderFifth (z : ℂ) : ℂ :=
  Complex.exp z - ∑ m ∈ Finset.range 5, z ^ m / (m.factorial : ℂ)

private lemma complexExpRemainderFifth_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖complexExpRemainderFifth z‖ ≤ Real.exp 1 * ‖z‖ ^ 5 := by
  unfold complexExpRemainderFifth
  calc
    ‖Complex.exp z - ∑ m ∈ Finset.range 5, z ^ m / (m.factorial : ℂ)‖
        ≤ ‖z‖ ^ 5 * Real.exp ‖z‖ :=
          Complex.norm_exp_sub_sum_le_norm_mul_exp z 5
    _ ≤ ‖z‖ ^ 5 * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz)
            (pow_nonneg (norm_nonneg z) 5)
    _ = Real.exp 1 * ‖z‖ ^ 5 := by ring

private def bellLocalTaylorConst : ℝ :=
  10000 * Real.exp 2

private lemma bellLocalTaylorConst_pos : 0 < bellLocalTaylorConst := by
  unfold bellLocalTaylorConst
  positivity

private lemma bellLocalExponent_fifth_remainder_norm_le {r θ : ℝ}
    (hr : 1 ≤ r) (hθ : |θ| ≤ 1) (hsmall : 2 * (r * |θ|) ≤ 1) :
    ‖bellLocalExponent r θ -
        (-Complex.I * ((bellSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((bellSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4)‖
      ≤ bellLocalTaylorConst * Real.exp r * r ^ 5 * |θ| ^ 5 := by
  let y : ℝ := |θ|
  let w : ℂ := (θ : ℂ) * Complex.I
  let u : ℂ := (r : ℂ) * (Complex.exp w - 1)
  let m : ℂ := (r : ℂ) * w
  let s2 : ℂ := (r : ℂ) * w ^ 2 / 2
  let s3 : ℂ := (r : ℂ) * w ^ 3 / 6
  let outer : ℂ := Complex.exp u - ∑ k ∈ Finset.range 3, u ^ k / (k.factorial : ℂ)
  let inner : ℂ := (r : ℂ) * ExpStirling.expLocalRemainder θ
  let cross : ℂ := (u ^ 2 - m ^ 2) / 2
  let outerPoly : ℂ := m ^ 3 / 6 + m ^ 2 * s2 / 2 + m ^ 4 / 24
  let innerPoly : ℂ := (r : ℂ) * (w ^ 3 / 6 + w ^ 4 / 24)
  let crossPoly : ℂ := m * s2 + m * s3 + s2 ^ 2 / 2
  let P : ℂ :=
    -Complex.I * ((bellSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
      ((bellSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg θ
  have hy1 : y ≤ 1 := by
    simpa [y] using hθ
  have hE2_ge_one : 1 ≤ Real.exp 2 := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hE1_le_E2 : Real.exp 1 ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)
  have hw_norm : ‖w‖ = y := by
    dsimp [w, y]
    simp
  have hm_norm : ‖m‖ = r * y := by
    dsimp [m]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hw_norm]
  have hs2_norm_le : ‖s2‖ ≤ r * y ^ 2 := by
    dsimp [s2]
    calc
      ‖(r : ℂ) * w ^ 2 / 2‖ = r * y ^ 2 / 2 := by
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0, norm_pow, hw_norm]
        norm_num
      _ ≤ r * y ^ 2 := by
        nlinarith [hr0, pow_nonneg hy0 2]
  have hs3_norm_le : ‖s3‖ ≤ r * y ^ 3 := by
    dsimp [s3]
    calc
      ‖(r : ℂ) * w ^ 3 / 6‖ = r * y ^ 3 / 6 := by
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0, norm_pow, hw_norm]
        norm_num
      _ ≤ r * y ^ 3 := by
        nlinarith [hr0, pow_nonneg hy0 3]
  have hu_norm : ‖u‖ ≤ 2 * (r * y) := by
    have hbase := bell_exp_i_sub_one_norm_le_two_abs hθ
    calc
      ‖u‖ = r * ‖Complex.exp w - 1‖ := by
        dsimp [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (2 * y) := by
        exact mul_le_mul_of_nonneg_left (by simpa [w, y] using hbase) hr0
      _ = 2 * (r * y) := by ring
  have hu_le_one : ‖u‖ ≤ 1 := hu_norm.trans hsmall
  have hs_norm_le : ‖u - m‖ ≤ r * y ^ 2 := by
    have hbase := bell_exp_i_sub_one_sub_id_norm_le_sq hθ
    have hdiff : u - m = (r : ℂ) *
        (Complex.exp w - 1 - (θ : ℂ) * Complex.I) := by
      dsimp [u, m, w]
      ring
    rw [hdiff]
    calc
      ‖(r : ℂ) * (Complex.exp w - 1 - (θ : ℂ) * Complex.I)‖
          = r * ‖Complex.exp w - 1 - (θ : ℂ) * Complex.I‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * y ^ 2 := by
        exact mul_le_mul_of_nonneg_left (by simpa [w, y] using hbase) hr0
  have htRest_norm_le :
      ‖u - m - s2‖ ≤ Real.exp 2 * r * y ^ 3 := by
    have hrest : u - m - s2 = (r : ℂ) * ExpStirling.expLocalRemainder θ := by
      dsimp [u, m, s2, w]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    rw [hrest]
    have hrem := ExpStirling.expLocalRemainder_norm_le_exp_one θ hθ
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 1 * y ^ 3) := by
        exact mul_le_mul_of_nonneg_left (by simpa [y] using hrem) hr0
      _ ≤ Real.exp 2 * r * y ^ 3 := by
        calc
          r * (Real.exp 1 * y ^ 3) = Real.exp 1 * (r * y ^ 3) := by ring
          _ ≤ Real.exp 2 * (r * y ^ 3) :=
            mul_le_mul_of_nonneg_right hE1_le_E2
              (mul_nonneg hr0 (pow_nonneg hy0 3))
          _ = Real.exp 2 * r * y ^ 3 := by ring
  have htFourth_norm_le :
      ‖u - m - s2 - s3‖ ≤ 2 * Real.exp 2 * r * y ^ 4 := by
    let t : ℂ := (r : ℂ) * expLocalRemainderFifth θ
    let s4 : ℂ := (r : ℂ) * w ^ 4 / 24
    have hrest : u - m - s2 - s3 = s4 + t := by
      dsimp [u, m, s2, s3, s4, t, w, expLocalRemainderFifth]
      rw [ExpStirling.expLocalRemainder_eq θ]
      ring_nf
      norm_num [Complex.ofReal_mul]
      ring
    have hs4 : ‖s4‖ ≤ r * y ^ 4 := by
      dsimp [s4]
      calc
        ‖(r : ℂ) * w ^ 4 / 24‖ = r * y ^ 4 / 24 := by
          rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hr0, norm_pow, hw_norm]
          norm_num
        _ ≤ r * y ^ 4 := by
          nlinarith [hr0, pow_nonneg hy0 4]
    have ht : ‖t‖ ≤ Real.exp 2 * r * y ^ 4 := by
      have hrem := expLocalRemainderFifth_norm_le
        (by linarith [hy1] : |θ| ≤ 2)
      dsimp [t]
      calc
        ‖(r : ℂ) * expLocalRemainderFifth θ‖
            = r * ‖expLocalRemainderFifth θ‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        _ ≤ r * (Real.exp 2 * y ^ 5) := by
          exact mul_le_mul_of_nonneg_left (by simpa [y] using hrem) hr0
        _ ≤ Real.exp 2 * r * y ^ 4 := by
          have hy5_le_y4 : y ^ 5 ≤ y ^ 4 := by
            calc
              y ^ 5 = y ^ 4 * y := by ring
              _ ≤ y ^ 4 * 1 :=
                mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy0 4)
              _ = y ^ 4 := by ring
          calc
            r * (Real.exp 2 * y ^ 5) = (Real.exp 2 * r) * y ^ 5 := by ring
            _ ≤ (Real.exp 2 * r) * y ^ 4 :=
              mul_le_mul_of_nonneg_left hy5_le_y4
                (mul_nonneg (Real.exp_pos 2).le hr0)
            _ = Real.exp 2 * r * y ^ 4 := by ring
    rw [hrest]
    calc
      ‖s4 + t‖ ≤ ‖s4‖ + ‖t‖ := norm_add_le _ _
      _ ≤ r * y ^ 4 + Real.exp 2 * r * y ^ 4 := add_le_add hs4 ht
      _ ≤ 2 * Real.exp 2 * r * y ^ 4 := by
        have hleft : r * y ^ 4 ≤ Real.exp 2 * r * y ^ 4 := by
          calc
            r * y ^ 4 = 1 * (r * y ^ 4) := by ring
            _ ≤ Real.exp 2 * (r * y ^ 4) :=
              mul_le_mul_of_nonneg_right hE2_ge_one
                (mul_nonneg hr0 (pow_nonneg hy0 4))
            _ = Real.exp 2 * r * y ^ 4 := by ring
        linarith
  have hW_decomp :
      bellLocalExponent r θ = Complex.exp (r : ℂ) * (outer + inner + cross) := by
    simpa [outer, inner, cross, u, m, w] using bellLocalExponent_decomp r θ
  have hP_decomp :
      P = Complex.exp (r : ℂ) * (outerPoly + innerPoly + crossPoly) := by
    dsimp [P, outerPoly, innerPoly, crossPoly, m, s2, s3, w,
      bellSaddleB3Real, bellSaddleB4Real]
    rw [← Complex.ofReal_exp r]
    ring_nf
    norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hdiff :
      bellLocalExponent r θ - P =
        Complex.exp (r : ℂ) *
          ((outer - outerPoly) + (inner - innerPoly) + (cross - crossPoly)) := by
    rw [hW_decomp, hP_decomp]
    ring
  have houter_eq :
      outer - outerPoly =
        complexExpRemainderFifth u +
          (u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6 +
            (u ^ 4 - m ^ 4) / 24 := by
    dsimp [outer, outerPoly, complexExpRemainderFifth]
    simp [Finset.sum_range_succ]
    ring
  have hcube_eq :
      u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2 =
        3 * m ^ 2 * (u - m - s2) + 3 * m * (u - m) ^ 2 + (u - m) ^ 3 := by
    ring
  have hcube_norm :
      ‖u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2‖ ≤
        20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
    rw [hcube_eq]
    have hraw :
        ‖3 * m ^ 2 * (u - m - s2) + 3 * m * (u - m) ^ 2 + (u - m) ^ 3‖
          ≤ 3 * ‖m‖ ^ 2 * ‖u - m - s2‖ +
            3 * ‖m‖ * ‖u - m‖ ^ 2 + ‖u - m‖ ^ 3 := by
      calc
        ‖3 * m ^ 2 * (u - m - s2) + 3 * m * (u - m) ^ 2 + (u - m) ^ 3‖
            ≤ ‖3 * m ^ 2 * (u - m - s2)‖ +
                ‖3 * m * (u - m) ^ 2‖ + ‖(u - m) ^ 3‖ := by
              calc
                ‖3 * m ^ 2 * (u - m - s2) + 3 * m * (u - m) ^ 2 +
                    (u - m) ^ 3‖
                    ≤ ‖3 * m ^ 2 * (u - m - s2) + 3 * m * (u - m) ^ 2‖ +
                        ‖(u - m) ^ 3‖ := norm_add_le _ _
                _ ≤ (‖3 * m ^ 2 * (u - m - s2)‖ +
                      ‖3 * m * (u - m) ^ 2‖) + ‖(u - m) ^ 3‖ :=
                    add_le_add (norm_add_le _ _) (le_refl _)
                _ = ‖3 * m ^ 2 * (u - m - s2)‖ +
                    ‖3 * m * (u - m) ^ 2‖ + ‖(u - m) ^ 3‖ := by ring
        _ = 3 * ‖m‖ ^ 2 * ‖u - m - s2‖ +
              3 * ‖m‖ * ‖u - m‖ ^ 2 + ‖u - m‖ ^ 3 := by
          simp [norm_pow]
    have hbound :
        3 * ‖m‖ ^ 2 * ‖u - m - s2‖ +
            3 * ‖m‖ * ‖u - m‖ ^ 2 + ‖u - m‖ ^ 3
          ≤ 20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
      have hm_le : ‖m‖ ≤ r * y := by rw [hm_norm]
      have hr3_le_r5 : r ^ 3 ≤ r ^ 5 := by
        have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hr, sq_nonneg r]
        calc
          r ^ 3 = r ^ 3 * 1 := by ring
          _ ≤ r ^ 3 * r ^ 2 :=
            mul_le_mul_of_nonneg_left h1_le_r2 (by positivity)
          _ = r ^ 5 := by ring
      have hy6_le_y5 : y ^ 6 ≤ y ^ 5 := by
        calc
          y ^ 6 = y ^ 5 * y := by ring
          _ ≤ y ^ 5 * 1 := mul_le_mul_of_nonneg_left hy1 (pow_nonneg hy0 5)
          _ = y ^ 5 := by ring
      calc
        3 * ‖m‖ ^ 2 * ‖u - m - s2‖ +
            3 * ‖m‖ * ‖u - m‖ ^ 2 + ‖u - m‖ ^ 3
            ≤ 3 * (r * y) ^ 2 * (Real.exp 2 * r * y ^ 3) +
                3 * (r * y) * (r * y ^ 2) ^ 2 +
                  (r * y ^ 2) ^ 3 := by
              gcongr
        _ ≤ 20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
          have hnon_r3 : 0 ≤ r ^ 3 := by positivity
          have hnon_y5 : 0 ≤ y ^ 5 := pow_nonneg hy0 5
          have h3plain :
              3 * r ^ 3 * y ^ 5 ≤ 3 * Real.exp 2 * r ^ 3 * y ^ 5 := by
            calc
              3 * r ^ 3 * y ^ 5 = 3 * (1 * (r ^ 3 * y ^ 5)) := by ring
              _ ≤ 3 * (Real.exp 2 * (r ^ 3 * y ^ 5)) := by
                gcongr
              _ = 3 * Real.exp 2 * r ^ 3 * y ^ 5 := by ring
          have hy6term :
              r ^ 3 * y ^ 6 ≤ Real.exp 2 * r ^ 3 * y ^ 5 := by
            calc
              r ^ 3 * y ^ 6 ≤ r ^ 3 * y ^ 5 :=
                mul_le_mul_of_nonneg_left hy6_le_y5 hnon_r3
              _ = 1 * (r ^ 3 * y ^ 5) := by ring
              _ ≤ Real.exp 2 * (r ^ 3 * y ^ 5) := by
                gcongr
              _ = Real.exp 2 * r ^ 3 * y ^ 5 := by ring
          calc
            3 * (r * y) ^ 2 * (Real.exp 2 * r * y ^ 3) +
                3 * (r * y) * (r * y ^ 2) ^ 2 + (r * y ^ 2) ^ 3
                = 3 * Real.exp 2 * r ^ 3 * y ^ 5 +
                    3 * r ^ 3 * y ^ 5 + r ^ 3 * y ^ 6 := by ring
            _ ≤ 3 * Real.exp 2 * r ^ 3 * y ^ 5 +
                3 * Real.exp 2 * r ^ 3 * y ^ 5 +
                  Real.exp 2 * r ^ 3 * y ^ 5 :=
                add_le_add (add_le_add (le_refl _) h3plain) hy6term
            _ = 7 * Real.exp 2 * r ^ 3 * y ^ 5 := by ring
            _ ≤ 20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
              gcongr
              norm_num
    exact hraw.trans hbound
  have hquartic_norm :
      ‖u ^ 4 - m ^ 4‖ ≤ 20 * r ^ 5 * y ^ 5 := by
    have hquartic_eq :
        u ^ 4 - m ^ 4 = (u - m) * (u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3) := by
      ring
    rw [hquartic_eq]
    have hsum :
        ‖u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3‖ ≤
          20 * r ^ 3 * y ^ 3 := by
      have hm_le : ‖m‖ ≤ r * y := by rw [hm_norm]
      have hu_le : ‖u‖ ≤ 2 * r * y := by
        simpa [mul_assoc] using hu_norm
      calc
        ‖u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3‖
            ≤ ‖u ^ 3‖ + ‖u ^ 2 * m‖ + ‖u * m ^ 2‖ + ‖m ^ 3‖ := by
              calc
                ‖u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3‖
                    ≤ ‖u ^ 3 + u ^ 2 * m + u * m ^ 2‖ + ‖m ^ 3‖ := norm_add_le _ _
                _ ≤ (‖u ^ 3 + u ^ 2 * m‖ + ‖u * m ^ 2‖) + ‖m ^ 3‖ :=
                    add_le_add (norm_add_le _ _) (le_refl _)
                _ ≤ ((‖u ^ 3‖ + ‖u ^ 2 * m‖) + ‖u * m ^ 2‖) + ‖m ^ 3‖ :=
                    add_le_add (add_le_add (norm_add_le _ _) (le_refl _)) (le_refl _)
                _ = ‖u ^ 3‖ + ‖u ^ 2 * m‖ + ‖u * m ^ 2‖ + ‖m ^ 3‖ := by ring
        _ = ‖u‖ ^ 3 + ‖u‖ ^ 2 * ‖m‖ + ‖u‖ * ‖m‖ ^ 2 + ‖m‖ ^ 3 := by
          simp [norm_pow]
        _ ≤ 20 * r ^ 3 * y ^ 3 := by
          calc
            ‖u‖ ^ 3 + ‖u‖ ^ 2 * ‖m‖ + ‖u‖ * ‖m‖ ^ 2 + ‖m‖ ^ 3
                ≤ (2 * r * y) ^ 3 + (2 * r * y) ^ 2 * (r * y) +
                    (2 * r * y) * (r * y) ^ 2 + (r * y) ^ 3 := by
                  gcongr
            _ ≤ 20 * r ^ 3 * y ^ 3 := by
              calc
                (2 * r * y) ^ 3 + (2 * r * y) ^ 2 * (r * y) +
                    (2 * r * y) * (r * y) ^ 2 + (r * y) ^ 3
                    = 15 * r ^ 3 * y ^ 3 := by ring
                _ ≤ 20 * r ^ 3 * y ^ 3 := by
                  gcongr
                  norm_num
    calc
      ‖(u - m) * (u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3)‖
          = ‖u - m‖ * ‖u ^ 3 + u ^ 2 * m + u * m ^ 2 + m ^ 3‖ := by rw [norm_mul]
      _ ≤ (r * y ^ 2) * (20 * r ^ 3 * y ^ 3) :=
          mul_le_mul hs_norm_le hsum (norm_nonneg _) (by positivity)
      _ ≤ 20 * r ^ 5 * y ^ 5 := by
        have hr4_le_r5 : r ^ 4 ≤ r ^ 5 := by
          calc
            r ^ 4 = r ^ 4 * 1 := by ring
            _ ≤ r ^ 4 * r :=
              mul_le_mul_of_nonneg_left hr (by positivity)
            _ = r ^ 5 := by ring
        nlinarith [hr4_le_r5, hy0, pow_nonneg hy0 5]
  have houter :
      ‖outer - outerPoly‖ ≤ 100 * Real.exp 2 * r ^ 5 * y ^ 5 := by
    rw [houter_eq]
    have htail :
        ‖complexExpRemainderFifth u‖ ≤ 32 * Real.exp 2 * r ^ 5 * y ^ 5 := by
      have htail0 := complexExpRemainderFifth_norm_le hu_le_one
      calc
        ‖complexExpRemainderFifth u‖ ≤ Real.exp 1 * ‖u‖ ^ 5 := htail0
        _ ≤ Real.exp 1 * (2 * (r * y)) ^ 5 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg u) hu_norm 5) (Real.exp_pos 1).le
        _ ≤ 32 * Real.exp 2 * r ^ 5 * y ^ 5 := by
          calc
            Real.exp 1 * (2 * (r * y)) ^ 5 =
                32 * Real.exp 1 * r ^ 5 * y ^ 5 := by ring
            _ ≤ 32 * Real.exp 2 * r ^ 5 * y ^ 5 := by
              gcongr
    calc
      ‖complexExpRemainderFifth u +
          (u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6 +
            (u ^ 4 - m ^ 4) / 24‖
          ≤ ‖complexExpRemainderFifth u‖ +
              ‖(u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖ +
                ‖(u ^ 4 - m ^ 4) / 24‖ := by
            calc
              ‖complexExpRemainderFifth u +
                  (u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6 +
                    (u ^ 4 - m ^ 4) / 24‖
                  ≤ ‖complexExpRemainderFifth u +
                      (u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖ +
                      ‖(u ^ 4 - m ^ 4) / 24‖ := norm_add_le _ _
              _ ≤ (‖complexExpRemainderFifth u‖ +
                    ‖(u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖) +
                    ‖(u ^ 4 - m ^ 4) / 24‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
              _ = ‖complexExpRemainderFifth u‖ +
                  ‖(u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖ +
                    ‖(u ^ 4 - m ^ 4) / 24‖ := by ring
      _ ≤ 32 * Real.exp 2 * r ^ 5 * y ^ 5 +
            20 * Real.exp 2 * r ^ 5 * y ^ 5 +
              20 * r ^ 5 * y ^ 5 := by
          have hcube_div :
              ‖(u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖ ≤
                20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
            calc
              ‖(u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2) / 6‖
                  ≤ ‖u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2‖ := by
                    rw [norm_div, Complex.norm_ofNat]
                    nlinarith [norm_nonneg (u ^ 3 - m ^ 3 - 3 * m ^ 2 * s2)]
              _ ≤ 20 * Real.exp 2 * r ^ 5 * y ^ 5 := hcube_norm
          have hquartic_div :
              ‖(u ^ 4 - m ^ 4) / 24‖ ≤ 20 * r ^ 5 * y ^ 5 := by
            calc
              ‖(u ^ 4 - m ^ 4) / 24‖ ≤ ‖u ^ 4 - m ^ 4‖ := by
                rw [norm_div, Complex.norm_ofNat]
                nlinarith [norm_nonneg (u ^ 4 - m ^ 4)]
              _ ≤ 20 * r ^ 5 * y ^ 5 := hquartic_norm
          exact add_le_add (add_le_add htail hcube_div) hquartic_div
      _ ≤ 100 * Real.exp 2 * r ^ 5 * y ^ 5 := by
        have hlast :
            20 * r ^ 5 * y ^ 5 ≤ 20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
          calc
            20 * r ^ 5 * y ^ 5 = 20 * (1 * (r ^ 5 * y ^ 5)) := by ring
            _ ≤ 20 * (Real.exp 2 * (r ^ 5 * y ^ 5)) := by
              gcongr
            _ = 20 * Real.exp 2 * r ^ 5 * y ^ 5 := by ring
        calc
          32 * Real.exp 2 * r ^ 5 * y ^ 5 +
              20 * Real.exp 2 * r ^ 5 * y ^ 5 + 20 * r ^ 5 * y ^ 5
              ≤ 32 * Real.exp 2 * r ^ 5 * y ^ 5 +
                  20 * Real.exp 2 * r ^ 5 * y ^ 5 +
                    20 * Real.exp 2 * r ^ 5 * y ^ 5 := by
                exact add_le_add (le_refl _) hlast
          _ = 72 * Real.exp 2 * r ^ 5 * y ^ 5 := by ring
          _ ≤ 100 * Real.exp 2 * r ^ 5 * y ^ 5 := by
            gcongr
            norm_num
  have hinner :
      ‖inner - innerPoly‖ ≤ Real.exp 2 * r ^ 5 * y ^ 5 := by
    have hinner_eq :
        inner - innerPoly = (r : ℂ) * expLocalRemainderFifth θ := by
      dsimp [inner, innerPoly, expLocalRemainderFifth]
      ring
    rw [hinner_eq]
    have hrem := expLocalRemainderFifth_norm_le
      (by linarith [hy1] : |θ| ≤ 2)
    calc
      ‖(r : ℂ) * expLocalRemainderFifth θ‖
          = r * ‖expLocalRemainderFifth θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 2 * y ^ 5) := by
        exact mul_le_mul_of_nonneg_left (by simpa [y] using hrem) hr0
      _ ≤ Real.exp 2 * r ^ 5 * y ^ 5 := by
        have hr_le_r5 : r ≤ r ^ 5 := by
          calc
            r = r * 1 := by ring
            _ ≤ r * r ^ 4 :=
              mul_le_mul_of_nonneg_left
                (by
                  have h1_le_r2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith [hr, sq_nonneg r]
                  calc
                    (1 : ℝ) = 1 * 1 := by ring
                    _ ≤ r ^ 2 * r ^ 2 :=
                      mul_le_mul h1_le_r2 h1_le_r2 zero_le_one (by positivity)
                    _ = r ^ 4 := by ring)
                hr0
            _ = r ^ 5 := by ring
        calc
          r * (Real.exp 2 * y ^ 5) = (Real.exp 2 * y ^ 5) * r := by ring
          _ ≤ (Real.exp 2 * y ^ 5) * r ^ 5 :=
            mul_le_mul_of_nonneg_left hr_le_r5
              (mul_nonneg (Real.exp_pos 2).le (pow_nonneg hy0 5))
          _ = Real.exp 2 * r ^ 5 * y ^ 5 := by ring
  have hcross :
      ‖cross - crossPoly‖ ≤ 10 * Real.exp 2 * r ^ 5 * y ^ 5 := by
    have hcross_eq :
        cross - crossPoly =
          m * (u - m - s2 - s3) + ((u - m) ^ 2 - s2 ^ 2) / 2 := by
      dsimp [cross, crossPoly]
      ring
    rw [hcross_eq]
    have hs_plus_s2 :
        ‖u - m + s2‖ ≤ 2 * r * y ^ 2 := by
      calc
        ‖u - m + s2‖ ≤ ‖u - m‖ + ‖s2‖ := norm_add_le _ _
        _ ≤ r * y ^ 2 + r * y ^ 2 := add_le_add hs_norm_le hs2_norm_le
        _ = 2 * r * y ^ 2 := by ring
    have hsquare_diff :
        ‖((u - m) ^ 2 - s2 ^ 2) / 2‖ ≤
          2 * Real.exp 2 * r ^ 2 * y ^ 5 := by
      have hsq_eq :
          (u - m) ^ 2 - s2 ^ 2 = (u - m - s2) * (u - m + s2) := by
        ring
      calc
        ‖((u - m) ^ 2 - s2 ^ 2) / 2‖
            ≤ ‖(u - m) ^ 2 - s2 ^ 2‖ := by
              rw [norm_div, Complex.norm_ofNat]
              norm_num
        _ = ‖(u - m - s2) * (u - m + s2)‖ := by rw [hsq_eq]
        _ = ‖u - m - s2‖ * ‖u - m + s2‖ := by rw [norm_mul]
        _ ≤ (Real.exp 2 * r * y ^ 3) * (2 * r * y ^ 2) :=
            mul_le_mul htRest_norm_le hs_plus_s2 (norm_nonneg _) (by positivity)
        _ = 2 * Real.exp 2 * r ^ 2 * y ^ 5 := by ring
    calc
      ‖m * (u - m - s2 - s3) + ((u - m) ^ 2 - s2 ^ 2) / 2‖
          ≤ ‖m * (u - m - s2 - s3)‖ +
              ‖((u - m) ^ 2 - s2 ^ 2) / 2‖ := norm_add_le _ _
      _ ≤ (r * y) * (2 * Real.exp 2 * r * y ^ 4) +
            2 * Real.exp 2 * r ^ 2 * y ^ 5 := by
          exact add_le_add
            (by
              rw [norm_mul, hm_norm]
              exact mul_le_mul_of_nonneg_left htFourth_norm_le (by positivity))
            hsquare_diff
      _ ≤ 10 * Real.exp 2 * r ^ 5 * y ^ 5 := by
        have hr2_le_r5 : r ^ 2 ≤ r ^ 5 := by
          calc
            r ^ 2 = r ^ 2 * 1 := by ring
            _ ≤ r ^ 2 * r ^ 3 :=
              mul_le_mul_of_nonneg_left
                (by
                  calc
                    (1 : ℝ) ≤ r := hr
                    _ ≤ r ^ 3 := by
                      nlinarith [hr, sq_nonneg r, show 0 ≤ r ^ 3 by positivity])
                (by positivity)
            _ = r ^ 5 := by ring
        calc
          (r * y) * (2 * Real.exp 2 * r * y ^ 4) +
              2 * Real.exp 2 * r ^ 2 * y ^ 5
              = 4 * Real.exp 2 * r ^ 2 * y ^ 5 := by ring
          _ ≤ 10 * Real.exp 2 * r ^ 5 * y ^ 5 := by
            have hnon : 0 ≤ Real.exp 2 * r ^ 2 * y ^ 5 := by positivity
            calc
              4 * Real.exp 2 * r ^ 2 * y ^ 5
                  ≤ 10 * Real.exp 2 * r ^ 2 * y ^ 5 := by
                    nlinarith
              _ ≤ 10 * Real.exp 2 * r ^ 5 * y ^ 5 := by
                    gcongr
  rw [show bellLocalExponent r θ -
        (-Complex.I * ((bellSaddleB3Real r : ℂ) / 6) * (θ : ℂ) ^ 3 +
          ((bellSaddleB4Real r : ℂ) / 24) * (θ : ℂ) ^ 4) =
        bellLocalExponent r θ - P by rfl]
  rw [hdiff]
  rw [norm_mul]
  have hexp_norm : ‖Complex.exp (r : ℂ)‖ = Real.exp r := by simp
  rw [hexp_norm]
  have hinside :
      ‖(outer - outerPoly) + (inner - innerPoly) + (cross - crossPoly)‖
        ≤ bellLocalTaylorConst * r ^ 5 * y ^ 5 := by
    calc
      ‖(outer - outerPoly) + (inner - innerPoly) + (cross - crossPoly)‖
          ≤ ‖outer - outerPoly‖ + ‖inner - innerPoly‖ + ‖cross - crossPoly‖ := by
            calc
              ‖(outer - outerPoly) + (inner - innerPoly) + (cross - crossPoly)‖
                  ≤ ‖(outer - outerPoly) + (inner - innerPoly)‖ +
                      ‖cross - crossPoly‖ := norm_add_le _ _
              _ ≤ (‖outer - outerPoly‖ + ‖inner - innerPoly‖) +
                    ‖cross - crossPoly‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
              _ = ‖outer - outerPoly‖ + ‖inner - innerPoly‖ +
                    ‖cross - crossPoly‖ := by ring
      _ ≤ 100 * Real.exp 2 * r ^ 5 * y ^ 5 +
            Real.exp 2 * r ^ 5 * y ^ 5 +
              10 * Real.exp 2 * r ^ 5 * y ^ 5 :=
          add_le_add (add_le_add houter hinner) hcross
      _ ≤ bellLocalTaylorConst * r ^ 5 * y ^ 5 := by
        unfold bellLocalTaylorConst
        calc
          100 * Real.exp 2 * r ^ 5 * y ^ 5 +
              Real.exp 2 * r ^ 5 * y ^ 5 +
                10 * Real.exp 2 * r ^ 5 * y ^ 5
              = 111 * (Real.exp 2 * r ^ 5 * y ^ 5) := by ring
          _ ≤ 10000 * (Real.exp 2 * r ^ 5 * y ^ 5) := by
            gcongr
            norm_num
          _ = 10000 * Real.exp 2 * r ^ 5 * y ^ 5 := by ring
  calc
    Real.exp r *
        ‖(outer - outerPoly) + (inner - innerPoly) + (cross - crossPoly)‖
        ≤ Real.exp r * (bellLocalTaylorConst * r ^ 5 * y ^ 5) :=
          mul_le_mul_of_nonneg_left hinside (Real.exp_pos r).le
    _ = bellLocalTaylorConst * Real.exp r * r ^ 5 * |θ| ^ 5 := by
      dsimp [y]
      ring

private lemma bellScaledRemainder_eq_unscaled {r x : ℝ}
    (hb : 0 < bellSaddleBReal r) :
    bellScaledRemainder r x =
      bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r)) -
        (-Complex.I * ((bellSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((bellSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 4) := by
  have hsqrt_ne : (Real.sqrt (bellSaddleBReal r) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hb_ne : (bellSaddleBReal r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hsqrt_sq := bell_sqrtB_sq hb
  have hsqrt_pow4 :
      (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 4 =
        (bellSaddleBReal r : ℂ) ^ 2 := by
    calc
      (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 4 =
          ((Real.sqrt (bellSaddleBReal r) : ℂ) ^ 2) ^ 2 := by ring
      _ = (bellSaddleBReal r : ℂ) ^ 2 := by rw [hsqrt_sq]
  have hθ3 :
      ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 3 =
        (x : ℂ) ^ 3 / (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 3 := by
    norm_num [Complex.ofReal_div]
    ring
  have hθ4 :
      ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 4 =
        (x : ℂ) ^ 4 / (Real.sqrt (bellSaddleBReal r) : ℂ) ^ 4 := by
    norm_num [Complex.ofReal_div]
    ring
  unfold bellScaledRemainder bellScaledCubic bellScaledQuartic
  rw [hθ3, hθ4, hsqrt_pow4]
  field_simp [hsqrt_ne, hb_ne]
  ring

private lemma bellScaledRemainder_norm_le {r x : ℝ}
    (hr : 1 ≤ r)
    (hθδ : |x / Real.sqrt (bellSaddleBReal r)| ≤ bellSaddleDeltaReal r)
    (hδle : bellSaddleDeltaReal r ≤ 1)
    (hsmall : 2 * (r * bellSaddleDeltaReal r) ≤ 1) :
    ‖bellScaledRemainder r x‖ ≤
      bellLocalTaylorConst * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  have hsqrt_pos : 0 < Real.sqrt (bellSaddleBReal r) := Real.sqrt_pos.mpr hbpos
  have hsqrt_ge : r * Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) :=
    bell_sqrtB_ge_r_exp_half hr
  have hθone : |x / Real.sqrt (bellSaddleBReal r)| ≤ 1 :=
    hθδ.trans hδle
  have hθsmall : 2 * (r * |x / Real.sqrt (bellSaddleBReal r)|) ≤ 1 := by
    calc
      2 * (r * |x / Real.sqrt (bellSaddleBReal r)|)
          ≤ 2 * (r * bellSaddleDeltaReal r) := by
            gcongr
      _ ≤ 1 := hsmall
  have hrem := bellLocalExponent_fifth_remainder_norm_le
    (r := r) (θ := x / Real.sqrt (bellSaddleBReal r)) hr hθone hθsmall
  rw [bellScaledRemainder_eq_unscaled hbpos]
  have hθ_abs_le :
      |x / Real.sqrt (bellSaddleBReal r)| ≤
        |x| / (r * Real.exp (r / 2)) := by
    rw [abs_div, abs_of_pos hsqrt_pos]
    exact div_le_div_of_nonneg_left (abs_nonneg x)
      (by positivity : 0 < r * Real.exp (r / 2)) hsqrt_ge
  have hθ5_le :
      |x / Real.sqrt (bellSaddleBReal r)| ^ 5 ≤
        (|x| / (r * Real.exp (r / 2))) ^ 5 :=
    pow_le_pow_left₀ (abs_nonneg _) hθ_abs_le 5
  calc
    ‖bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r)) -
        (-Complex.I * ((bellSaddleB3Real r : ℂ) / 6) *
            ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 3 +
          ((bellSaddleB4Real r : ℂ) / 24) *
            ((x / Real.sqrt (bellSaddleBReal r) : ℝ) : ℂ) ^ 4)‖
        ≤ bellLocalTaylorConst * Real.exp r * r ^ 5 *
            |x / Real.sqrt (bellSaddleBReal r)| ^ 5 := hrem
    _ ≤ bellLocalTaylorConst * Real.exp r * r ^ 5 *
          (|x| / (r * Real.exp (r / 2))) ^ 5 := by
        exact mul_le_mul_of_nonneg_left hθ5_le
          (mul_nonneg
            (mul_nonneg bellLocalTaylorConst_pos.le (Real.exp_pos r).le)
            (pow_nonneg hrpos.le 5))
    _ = bellLocalTaylorConst * Real.exp (-(3 / 2 : ℝ) * r) * |x| ^ 5 := by
        have hr_ne : r ≠ 0 := hrpos.ne'
        have hexp_ne : Real.exp (r / 2) ≠ 0 := (Real.exp_pos (r / 2)).ne'
        field_simp [hr_ne, hexp_ne]
        rw [show (Real.exp (r / 2)) ^ 5 = Real.exp (5 * (r / 2)) by
          rw [← Real.exp_nat_mul]
          norm_num]
        have hexp_calc :
            Real.exp (5 * (r / 2)) * Real.exp (-(r * 3 / 2)) = Real.exp r := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          bellLocalTaylorConst * Real.exp r * |x| ^ 5 =
              bellLocalTaylorConst * |x| ^ 5 *
                (Real.exp (5 * (r / 2)) * Real.exp (-(r * 3 / 2))) := by
                rw [hexp_calc]
                ring
          _ = bellLocalTaylorConst * |x| ^ 5 * Real.exp (5 * (r / 2)) *
                Real.exp (-(r * 3 / 2)) := by ring

private lemma complex_exp_second_error_bound (C Q R W : ℂ)
    (hW : W = C + Q + R) (hWnorm : ‖W‖ ≤ 1) :
    ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
      Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
        (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
  have hsum :
      (∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)) =
        1 + W + W ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have htail :
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ ≤ Real.exp 1 * ‖W‖ ^ 3 := by
    calc
      ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ =
          ‖Complex.exp W - ∑ m ∈ Finset.range 3, W ^ m / (m.factorial : ℂ)‖ := by
            rw [hsum]
      _ ≤ ‖W‖ ^ 3 * Real.exp ‖W‖ :=
        Complex.norm_exp_sub_sum_le_norm_mul_exp W 3
      _ ≤ ‖W‖ ^ 3 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hWnorm) (pow_nonneg (norm_nonneg W) 3)
      _ = Real.exp 1 * ‖W‖ ^ 3 := by ring
  have hdecomp :
      Complex.exp W - (1 + C + Q + C ^ 2 / 2) =
        (Complex.exp W - (1 + W + W ^ 2 / 2)) +
          (R + (W ^ 2 - C ^ 2) / 2) := by
    rw [hW]
    ring
  rw [hdecomp]
  calc
    ‖(Complex.exp W - (1 + W + W ^ 2 / 2)) + (R + (W ^ 2 - C ^ 2) / 2)‖
        ≤ ‖Complex.exp W - (1 + W + W ^ 2 / 2)‖ +
            ‖R + (W ^ 2 - C ^ 2) / 2‖ := norm_add_le _ _
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖(W ^ 2 - C ^ 2) / 2‖) := by
      exact add_le_add htail (norm_add_le _ _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + (‖R‖ + ‖W ^ 2 - C ^ 2‖) := by
      have hhalf : ‖(W ^ 2 - C ^ 2) / 2‖ ≤ ‖W ^ 2 - C ^ 2‖ := by
        rw [norm_div, Complex.norm_ofNat]
        nlinarith [norm_nonneg (W ^ 2 - C ^ 2)]
      exact add_le_add (le_refl _) (add_le_add_right hhalf _)
    _ ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
          (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
      have hsq :
          W ^ 2 - C ^ 2 = (Q + R) * (2 * C + Q + R) := by
        rw [hW]
        ring
      have hprod :
          ‖W ^ 2 - C ^ 2‖ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
        rw [hsq]
        calc
          ‖(Q + R) * (2 * C + Q + R)‖ =
              ‖Q + R‖ * ‖2 * C + Q + R‖ := by rw [norm_mul]
          _ ≤ (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := by
            have hQR : ‖Q + R‖ ≤ ‖Q‖ + ‖R‖ := norm_add_le _ _
            have h2C : ‖(2 : ℂ) * C‖ = 2 * ‖C‖ := by
              rw [norm_mul, Complex.norm_ofNat]
            have hCQR : ‖2 * C + Q + R‖ ≤ 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by
              calc
                ‖2 * C + Q + R‖ ≤ ‖2 * C + Q‖ + ‖R‖ := norm_add_le _ _
                _ ≤ (‖2 * C‖ + ‖Q‖) + ‖R‖ :=
                  add_le_add (norm_add_le _ _) (le_refl _)
                _ = 2 * ‖C‖ + ‖Q‖ + ‖R‖ := by rw [h2C]
            exact mul_le_mul hQR hCQR (norm_nonneg _) (by positivity)
      nlinarith [hprod]

private def bellGaussianDom (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2) / 2) *
    (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
      |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)

private lemma bellGaussianDom_nonneg (x : ℝ) : 0 ≤ bellGaussianDom x := by
  unfold bellGaussianDom
  positivity

private lemma gaussian_abs_monomial_integrable (k : ℕ) :
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

private lemma bellGaussianDom_integrable : Integrable bellGaussianDom := by
  let g : ℕ → ℝ → ℝ := fun k x => Real.exp (-(x ^ 2) / 2) * |x| ^ k
  have hsum :
      Integrable (fun x : ℝ =>
        g 5 x + g 6 x + g 7 x + g 8 x + g 9 x + g 10 x +
          g 11 x + g 12 x + g 13 x + g 14 x + g 15 x) := by
    simpa [g, add_assoc] using
      ((((((((((gaussian_abs_monomial_integrable 5).add
        (gaussian_abs_monomial_integrable 6)).add
        (gaussian_abs_monomial_integrable 7)).add
        (gaussian_abs_monomial_integrable 8)).add
        (gaussian_abs_monomial_integrable 9)).add
        (gaussian_abs_monomial_integrable 10)).add
        (gaussian_abs_monomial_integrable 11)).add
        (gaussian_abs_monomial_integrable 12)).add
        (gaussian_abs_monomial_integrable 13)).add
        (gaussian_abs_monomial_integrable 14)).add
        (gaussian_abs_monomial_integrable 15)
  convert hsum using 1
  ext x
  unfold bellGaussianDom
  dsimp [g]
  ring_nf

private lemma bellGaussianDom_integral_nonneg :
    0 ≤ ∫ x : ℝ, bellGaussianDom x := by
  exact integral_nonneg (fun x => bellGaussianDom_nonneg x)

private def bellLocalL1Const : ℝ :=
  27 * Real.exp 1 * (20 + bellLocalTaylorConst) ^ 3 + bellLocalTaylorConst +
    6 * (10 + bellLocalTaylorConst) * (30 + bellLocalTaylorConst)

private lemma bellLocalL1Const_pos : 0 < bellLocalL1Const := by
  unfold bellLocalL1Const bellLocalTaylorConst
  positivity

private lemma bell_local_integrand_bound {r x : ℝ}
    (hr : 1 ≤ r)
    (hθδ : |x / Real.sqrt (bellSaddleBReal r)| ≤ bellSaddleDeltaReal r)
    (hδle : bellSaddleDeltaReal r ≤ 1)
    (hsmall : 2 * (r * bellSaddleDeltaReal r) ≤ 1)
    (hWnorm : ‖bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r))‖ ≤ 1) :
    ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖
      ≤ bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r) * bellGaussianDom x := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : 0 ≤ r := hrpos.le
  have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
  let C : ℂ := bellScaledCubic r x
  let Q : ℂ := bellScaledQuartic r x
  let R : ℂ := bellScaledRemainder r x
  let W : ℂ := bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r))
  let y : ℝ := |x|
  let A : ℝ := Real.exp (-(r / 2))
  let B : ℝ := Real.exp (-r)
  let D : ℝ := Real.exp (-(3 / 2 : ℝ) * r)
  let K : ℝ := bellLocalTaylorConst
  let S : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
  let T : ℝ := (10 * y ^ 4 + K * y ^ 5) * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)
  let G : ℝ := y ^ 5 + y ^ 6 + y ^ 7 + y ^ 8 + y ^ 9 + y ^ 10 +
    y ^ 11 + y ^ 12 + y ^ 13 + y ^ 14 + y ^ 15
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact bellLocalTaylorConst_pos.le
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact abs_nonneg x
  have hA_nonneg : 0 ≤ A := by dsimp [A]; positivity
  have hB_nonneg : 0 ≤ B := by dsimp [B]; positivity
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hB_le_A : B ≤ A := by
    dsimp [A, B]
    exact Real.exp_le_exp.mpr (by nlinarith [hr0])
  have hD_le_A : D ≤ A := by
    dsimp [A, D]
    exact Real.exp_le_exp.mpr (by nlinarith [hr0])
  have hD_le_B : D ≤ B := by
    dsimp [B, D]
    exact Real.exp_le_exp.mpr (by nlinarith [hr0])
  have hA_mul_B : A * B = D := by
    dsimp [A, B, D]
    rw [← Real.exp_add]
    congr 1
    ring
  have hA_cube : A ^ 3 = D := by
    dsimp [A, D]
    rw [show (Real.exp (-(r / 2))) ^ 3 = Real.exp (3 * (-(r / 2))) by
      rw [← Real.exp_nat_mul]
      norm_num]
    congr 1
    ring
  have hWsplit : W = C + Q + R := by
    dsimp [W, C, Q, R]
    exact bellLocalExponent_scaled_split r x
  have hP :
      saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x =
        1 + C + Q + C ^ 2 / 2 := by
    dsimp [C, Q]
    exact bell_saddleSecondPoly_eq_scaled_terms hbpos
  have herr := complex_exp_second_error_bound C Q R W hWsplit (by simpa [W] using hWnorm)
  have hC : ‖C‖ ≤ 10 * A * y ^ 3 := by
    dsimp [C, A, y]
    simpa [mul_assoc] using bellScaledCubic_norm_le (r := r) (x := x) hr
  have hQ_B : ‖Q‖ ≤ 10 * B * y ^ 4 := by
    dsimp [Q, B, y]
    simpa [mul_assoc] using bellScaledQuartic_norm_le (r := r) (x := x) hr
  have hQ_A : ‖Q‖ ≤ 10 * A * y ^ 4 := by
    exact hQ_B.trans (by gcongr)
  have hR_D : ‖R‖ ≤ K * D * y ^ 5 := by
    dsimp [R, K, D, y]
    simpa [mul_assoc] using
      bellScaledRemainder_norm_le (r := r) (x := x) hr hθδ hδle hsmall
  have hR_A : ‖R‖ ≤ K * A * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hR_B : ‖R‖ ≤ K * B * y ^ 5 := by
    exact hR_D.trans (by gcongr)
  have hWpoly : ‖W‖ ≤ A * S := by
    calc
      ‖W‖ = ‖C + Q + R‖ := by rw [hWsplit]
      _ ≤ ‖C‖ + ‖Q‖ + ‖R‖ := by
        calc
          ‖C + Q + R‖ ≤ ‖C + Q‖ + ‖R‖ := norm_add_le _ _
          _ ≤ (‖C‖ + ‖Q‖) + ‖R‖ := add_le_add (norm_add_le _ _) (le_refl _)
          _ = ‖C‖ + ‖Q‖ + ‖R‖ := by ring
      _ ≤ 10 * A * y ^ 3 + 10 * A * y ^ 4 + K * A * y ^ 5 :=
        add_le_add (add_le_add hC hQ_A) hR_A
      _ = A * S := by
        dsimp [S]
        ring
  have hWcube :
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * D * S ^ 3 := by
    calc
      Real.exp 1 * ‖W‖ ^ 3 ≤ Real.exp 1 * (A * S) ^ 3 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg W) hWpoly 3) (Real.exp_pos 1).le
      _ = Real.exp 1 * D * S ^ 3 := by
        rw [mul_pow, hA_cube]
        ring
  have hQR : ‖Q‖ + ‖R‖ ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
    calc
      ‖Q‖ + ‖R‖ ≤ 10 * B * y ^ 4 + K * B * y ^ 5 := add_le_add hQ_B hR_B
      _ = B * (10 * y ^ 4 + K * y ^ 5) := by ring
  have hCQR : 2 * ‖C‖ + ‖Q‖ + ‖R‖ ≤ A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by
    calc
      2 * ‖C‖ + ‖Q‖ + ‖R‖
          ≤ 2 * (10 * A * y ^ 3) + 10 * A * y ^ 4 + K * A * y ^ 5 := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)) hQ_A) hR_A
      _ = A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5) := by ring
  have hprod :
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) ≤ D * T := by
    calc
      (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖)
          ≤ (B * (10 * y ^ 4 + K * y ^ 5)) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) := by
            have hupper_nonneg : 0 ≤ B * (10 * y ^ 4 + K * y ^ 5) := by
              positivity
            exact mul_le_mul hQR hCQR (by positivity) hupper_nonneg
      _ = D * T := by
        dsimp [T]
        rw [show B * (10 * y ^ 4 + K * y ^ 5) *
              (A * (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) =
              (A * B) * ((10 * y ^ 4 + K * y ^ 5) *
                (20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5)) by ring]
        rw [hA_mul_B]
  have hpoly :
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T ≤ bellLocalL1Const * G := by
    have hK20_nonneg : 0 ≤ 20 + K := by positivity
    have hK10_nonneg : 0 ≤ 10 + K := by positivity
    have hK30_nonneg : 0 ≤ 30 + K := by positivity
    have hY345_nonneg : 0 ≤ y ^ 3 + y ^ 4 + y ^ 5 := by positivity
    have hY45_nonneg : 0 ≤ y ^ 4 + y ^ 5 := by positivity
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      positivity
    have hy5_le_G : y ^ 5 ≤ G := by
      dsimp [G]
      nlinarith [pow_nonneg hy0 6, pow_nonneg hy0 7, pow_nonneg hy0 8,
        pow_nonneg hy0 9, pow_nonneg hy0 10, pow_nonneg hy0 11,
        pow_nonneg hy0 12, pow_nonneg hy0 13, pow_nonneg hy0 14,
        pow_nonneg hy0 15]
    have hcube_support :
        (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 ≤ 27 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10,
        pow_nonneg hy0 11, pow_nonneg hy0 12, pow_nonneg hy0 13,
        pow_nonneg hy0 14, pow_nonneg hy0 15]
    have hprod_support :
        (y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5) ≤ 6 * G := by
      dsimp [G]
      ring_nf
      nlinarith [pow_nonneg hy0 5, pow_nonneg hy0 6, pow_nonneg hy0 7,
        pow_nonneg hy0 8, pow_nonneg hy0 9, pow_nonneg hy0 10]
    have hS_le : S ≤ (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
      dsimp [S]
      calc
        10 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
            ≤ (20 + K) * y ^ 3 + (20 + K) * y ^ 4 + (20 + K) * y ^ 5 := by
              gcongr
              · linarith
              · linarith
              · linarith
        _ = (20 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
    have hS_cube :
        S ^ 3 ≤ (20 + K) ^ 3 * (27 * G) := by
      calc
        S ^ 3 ≤ ((20 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) hS_le 3
        _ = (20 + K) ^ 3 * (y ^ 3 + y ^ 4 + y ^ 5) ^ 3 := by ring
        _ ≤ (20 + K) ^ 3 * (27 * G) :=
          mul_le_mul_of_nonneg_left hcube_support (pow_nonneg hK20_nonneg 3)
    have hT_le :
        T ≤ (10 + K) * (30 + K) * (6 * G) := by
      have hleft : 10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * (y ^ 4 + y ^ 5) := by
        calc
          10 * y ^ 4 + K * y ^ 5 ≤ (10 + K) * y ^ 4 + (10 + K) * y ^ 5 := by
            gcongr
            · linarith
            · linarith
          _ = (10 + K) * (y ^ 4 + y ^ 5) := by ring
      have hright :
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5 ≤
            (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by
        calc
          20 * y ^ 3 + 10 * y ^ 4 + K * y ^ 5
              ≤ (30 + K) * y ^ 3 + (30 + K) * y ^ 4 + (30 + K) * y ^ 5 := by
                gcongr
                · linarith
                · linarith
                · linarith
          _ = (30 + K) * (y ^ 3 + y ^ 4 + y ^ 5) := by ring
      calc
        T ≤ ((10 + K) * (y ^ 4 + y ^ 5)) *
              ((30 + K) * (y ^ 3 + y ^ 4 + y ^ 5)) := by
          dsimp [T]
          exact mul_le_mul hleft hright (by positivity) (by positivity)
        _ = (10 + K) * (30 + K) *
              ((y ^ 4 + y ^ 5) * (y ^ 3 + y ^ 4 + y ^ 5)) := by ring
        _ ≤ (10 + K) * (30 + K) * (6 * G) := by
          gcongr
    calc
      Real.exp 1 * S ^ 3 + K * y ^ 5 + T
          ≤ Real.exp 1 * ((20 + K) ^ 3 * (27 * G)) + K * G +
              (10 + K) * (30 + K) * (6 * G) := by
            exact add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left hS_cube (Real.exp_pos 1).le)
              (mul_le_mul_of_nonneg_left hy5_le_G hK_nonneg)) hT_le
      _ = (27 * Real.exp 1 * (20 + K) ^ 3 + K +
            6 * (10 + K) * (30 + K)) * G := by ring
      _ = bellLocalL1Const * G := by
        dsimp [K]
        unfold bellLocalL1Const
        ring
  have hdiff :
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖ ≤
        bellLocalL1Const * D * G := by
    calc
      ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
          ≤ Real.exp 1 * ‖W‖ ^ 3 + ‖R‖ +
              (‖Q‖ + ‖R‖) * (2 * ‖C‖ + ‖Q‖ + ‖R‖) := herr
      _ ≤ Real.exp 1 * D * S ^ 3 + K * D * y ^ 5 + D * T := by
        exact add_le_add (add_le_add hWcube hR_D) hprod
      _ = D * (Real.exp 1 * S ^ 3 + K * y ^ 5 + T) := by ring
      _ ≤ D * (bellLocalL1Const * G) :=
        mul_le_mul_of_nonneg_left hpoly hD_nonneg
      _ = bellLocalL1Const * D * G := by ring
  rw [bell_saddleLocalRatio_eq]
  rw [hP]
  change
    ‖Complex.exp (-(x ^ 2) / 2) *
        (Complex.exp W - (1 + C + Q + C ^ 2 / 2))‖ ≤
      bellLocalL1Const * D * bellGaussianDom x
  rw [norm_mul]
  have hgauss :
      ‖Complex.exp (-(x ^ 2) / 2)‖ = Real.exp (-(x ^ 2) / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two]
  rw [hgauss]
  unfold bellGaussianDom
  dsimp [D, G, y]
  calc
    Real.exp (-(x ^ 2) / 2) *
        ‖Complex.exp W - (1 + C + Q + C ^ 2 / 2)‖
        ≤ Real.exp (-(x ^ 2) / 2) * (bellLocalL1Const * D * G) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le
    _ = bellLocalL1Const * D *
        (Real.exp (-(x ^ 2) / 2) *
          (|x| ^ 5 + |x| ^ 6 + |x| ^ 7 + |x| ^ 8 + |x| ^ 9 + |x| ^ 10 +
            |x| ^ 11 + |x| ^ 12 + |x| ^ 13 + |x| ^ 14 + |x| ^ 15)) := by
      ring

private lemma bell_local_integrand_continuous (r : ℝ) :
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

private lemma bellGaussianDom_continuous : Continuous bellGaussianDom := by
  unfold bellGaussianDom
  fun_prop

private lemma bellGaussianDom_window_le_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in -L..L, bellGaussianDom x) ≤ ∫ x : ℝ, bellGaussianDom x := by
  have hle : -L ≤ L := by linarith
  rw [intervalIntegral.integral_of_le hle]
  exact setIntegral_le_integral bellGaussianDom_integrable
    (Eventually.of_forall bellGaussianDom_nonneg)

/--
Bell-specific hard local estimate: the fifth-order expansion of
`exp (exp (r e^{iθ}) - exp r - i a(r)θ + b(r)θ²/2)` after the scaling
`θ = x / sqrt (b(r))`, with the cubic, quartic, and sextic Gaussian correction
subtracted, is `L¹-o(bellSecondCorrScale r)`.

This is the only intentionally isolated analytic gap in this file.  It is the
same local Taylor/Gaussian-domination estimate as the involution proof, but with
the nested exponential Bell saddle algebra.
-/
theorem bell_local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
          (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
          bellSecondCorrScale r)
      atTop (𝓝 0) := by
  let M : ℝ := ∫ x : ℝ, bellGaussianDom x
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact bellGaussianDom_integral_nonneg
  have hsmall_u :
      ∀ᶠ r : ℝ in atTop, 2 * (r * bellSaddleDeltaReal r) ≤ 1 := by
    have ht : Tendsto (fun r : ℝ => 2 * (r * bellSaddleDeltaReal r)) atTop (𝓝 0) := by
      simpa using (bell_r_delta_tendsto_zero.const_mul (2 : ℝ))
    exact ht.eventually_le_const zero_lt_one
  have hupper_tendsto :
      Tendsto
        (fun r : ℝ =>
          8 * bellLocalL1Const * M * Real.exp (-(1 / 2 : ℝ) * r))
        atTop (𝓝 0) := by
    have hlin : Tendsto (fun r : ℝ => (-(1 / 2 : ℝ)) * r) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0) tendsto_id
    have hexp : Tendsto (fun r : ℝ => Real.exp ((-(1 / 2 : ℝ)) * r)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hlin
    simpa [mul_assoc] using hexp.const_mul (8 * bellLocalL1Const * M)
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
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖ :=
      intervalIntegral.integral_nonneg hle (fun _ _ => norm_nonneg _)
    exact div_nonneg hint_nonneg hcorr.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), bell_delta_le_one_eventually,
      bell_local_exponent_norm_le_eventually,
      bellLocalBound_tendsto_zero.eventually_le_const zero_lt_one,
      hsmall_u, bellSecondCorrScale_lower_exp_eventually,
      bellSecondCorrScale_pos_eventually] with
      r hr hδle hloc hlocSmall hsmall hcorrLower hcorrPos
    let L : ℝ := bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)
    let F : ℝ → ℝ := fun x =>
      ‖Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r
            (x / Real.sqrt (bellSaddleBReal r)) -
          saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖
    let H : ℝ → ℝ := fun x =>
      (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * bellGaussianDom x
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hbpos : 0 < bellSaddleBReal r := bellSaddleBReal_pos_of_ge_one hr
    have hsqrt_pos : 0 < Real.sqrt (bellSaddleBReal r) := Real.sqrt_pos.mpr hbpos
    have hδnonneg : 0 ≤ bellSaddleDeltaReal r := by
      unfold bellSaddleDeltaReal
      positivity
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    have hle : -L ≤ L := by linarith
    have hpoint : ∀ x ∈ Set.Icc (-L) L, F x ≤ H x := by
      intro x hx
      have hxabs : |x| ≤ L := by
        exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hθδ : |x / Real.sqrt (bellSaddleBReal r)| ≤ bellSaddleDeltaReal r := by
        rw [abs_div, abs_of_pos hsqrt_pos]
        calc
          |x| / Real.sqrt (bellSaddleBReal r) ≤
              L / Real.sqrt (bellSaddleBReal r) :=
            div_le_div_of_nonneg_right hxabs hsqrt_pos.le
          _ = bellSaddleDeltaReal r := by
            dsimp [L]
            field_simp [hsqrt_pos.ne']
      have hWnorm :
          ‖bellLocalExponent r (x / Real.sqrt (bellSaddleBReal r))‖ ≤ 1 :=
        (hloc (x / Real.sqrt (bellSaddleBReal r)) hθδ).trans hlocSmall
      have hb := bell_local_integrand_bound hr hθδ hδle hsmall hWnorm
      dsimp [F, H]
      exact hb
    have hFint : IntervalIntegrable F volume (-L) L := by
      exact (bell_local_integrand_continuous r).intervalIntegrable _ _
    have hHint : IntervalIntegrable H volume (-L) L := by
      exact (bellGaussianDom_continuous.const_mul
        (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r))).intervalIntegrable _ _
    have hIntBound :
        (∫ x in -L..L, F x) ≤
          (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M := by
      have hconst_nonneg :
          0 ≤ bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r) :=
        mul_nonneg bellLocalL1Const_pos.le (Real.exp_pos _).le
      calc
        (∫ x in -L..L, F x) ≤ ∫ x in -L..L, H x :=
          intervalIntegral.integral_mono_on hle hFint hHint hpoint
        _ = (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) *
              (∫ x in -L..L, bellGaussianDom x) := by
          dsimp [H]
          rw [intervalIntegral.integral_const_mul]
        _ ≤ (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M := by
          exact mul_le_mul_of_nonneg_left
            (by dsimp [M]; exact bellGaussianDom_window_le_integral hLnonneg)
            hconst_nonneg
    have hnum_nonneg :
        0 ≤ (bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M :=
      mul_nonneg
        (mul_nonneg bellLocalL1Const_pos.le (Real.exp_pos _).le) hM_nonneg
    have hscale_pos : 0 < (1 / 8 : ℝ) * Real.exp (-r) := by positivity
    have hmain :
        (∫ x in -L..L, F x) / bellSecondCorrScale r ≤
          ((bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
            ((1 / 8 : ℝ) * Real.exp (-r)) := by
      calc
        (∫ x in -L..L, F x) / bellSecondCorrScale r
            ≤ ((bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
                bellSecondCorrScale r :=
              div_le_div_of_nonneg_right hIntBound hcorrPos.le
        _ ≤ ((bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
              ((1 / 8 : ℝ) * Real.exp (-r)) :=
            div_le_div_of_nonneg_left hnum_nonneg hscale_pos hcorrLower
    calc
      ((∫ x in -(bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))..
          (bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
                bellSaddleAReal bellSaddleBReal r
                (x / Real.sqrt (bellSaddleBReal r)) -
              saddleSecondPoly bellSaddleBReal bellSaddleB3Real bellSaddleB4Real r x)‖) /
          bellSecondCorrScale r)
          = (∫ x in -L..L, F x) / bellSecondCorrScale r := by rfl
      _ ≤ ((bellLocalL1Const * Real.exp (-(3 / 2 : ℝ) * r)) * M) /
            ((1 / 8 : ℝ) * Real.exp (-r)) := hmain
      _ = 8 * bellLocalL1Const * M * Real.exp (-(1 / 2 : ℝ) * r) := by
        have hexp_ne : Real.exp (-r) ≠ 0 := (Real.exp_pos (-r)).ne'
        field_simp [hexp_ne]
        have hexp_calc' :
            Real.exp (-(3 * r / 2)) =
              Real.exp (-(r / 2)) * Real.exp (-r) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp_calc']
        ring

/-- The produced second-order H-admissible Bell instance. -/
def bellSecondOrderHAdmissible : SecondOrderHAdmissible bellHAdmissible where
  b3 := bellSaddleB3Real
  b4 := bellSaddleB4Real
  corrScale := bellSecondCorrScale
  corrScale_pos := by
    simpa [bellHAdmissible] using bellSecondCorrScale_pos_eventually
  corrScale_tendsto_zero := by
    simpa [bellHAdmissible] using bellSecondCorrScale_tendsto_zero
  corrScale_dominates_correction := by
    refine ⟨1, by norm_num, ?_⟩
    exact Eventually.of_forall fun r => by
      simp [bellHAdmissible, bellSecondCorrScale]
  local_second_L1 := by
    simpa [bellHAdmissible] using bell_local_second_L1
  tail_second_uniform := by
    simpa [bellHAdmissible] using bell_tail_second_uniform


