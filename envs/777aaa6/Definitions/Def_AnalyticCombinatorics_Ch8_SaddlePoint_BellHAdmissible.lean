-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:19:20.83306+00:00
-- url     : https://prove2.me/theorems/963fbc4d-74fc-4a8a-a5cd-6dd819f55a7e
-- title:
--   Bell saddle functions and admissibility records
-- statement:
--   The Bell mean is r exp(r), variance r(r+1)exp(r), and window exp(-2r/5). A chosen nonnegative root solves r exp(r)=n. Explicit local exponent, polynomial-exponential control, constants and exp(-r) tail control supply the Bell admissibility record and its saddle sequence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/BellHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
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
# Bell H-admissible saddle data

This file records the continuous Hayman data for
`exp (exp z - 1)`.  The saddle is normalized by
`a r = r exp r`, `b r = r (r + 1) exp r`, with the window
`δ r = exp (-(2/5) r)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The Bell formal series used by the H-admissible interface. -/
noncomputable abbrev bellSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  analyticBellSeries

/-- Continuous Bell saddle mean, `a(r)=r e^r`. -/
def bellSaddleAReal (r : ℝ) : ℝ :=
  r * Real.exp r

/-- Continuous Bell saddle variance scale, `b(r)=r(r+1)e^r`. -/
def bellSaddleBReal (r : ℝ) : ℝ :=
  r * (r + 1) * Real.exp r

/-- Hayman window for the Bell saddle. -/
def bellSaddleDeltaReal (r : ℝ) : ℝ :=
  Real.exp (-(2 / 5 : ℝ) * r)

@[simp] lemma bellSaddleAReal_apply (r : ℝ) :
    bellSaddleAReal r = r * Real.exp r := rfl

@[simp] lemma bellSaddleBReal_apply (r : ℝ) :
    bellSaddleBReal r = r * (r + 1) * Real.exp r := rfl

@[simp] lemma bellSaddleDeltaReal_apply (r : ℝ) :
    bellSaddleDeltaReal r = Real.exp (-(2 / 5 : ℝ) * r) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def bellLocalExponent (r θ : ℝ) : ℂ :=
  Complex.exp ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) -
    Complex.exp (r : ℂ) -
      ((bellSaddleAReal r * θ : ℝ) : ℂ) * Complex.I +
        ((bellSaddleBReal r * θ ^ 2 / 2 : ℝ) : ℂ)

lemma bell_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
        bellSaddleAReal bellSaddleBReal r θ =
      Complex.exp (bellLocalExponent r θ) := by
  set_option backward.isDefEq.respectTransparency false in
    unfold saddleLocalRatio bellLocalExponent bellSaddleAReal bellSaddleBReal
    rw [← Complex.exp_sub]
    rw [← Complex.exp_add]
    rw [← Complex.exp_sub]
    congr 1
    ring_nf

lemma bell_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop,
      0 < ((fun z : ℂ => Complex.exp (Complex.exp z - 1)) (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  change 0 < (Complex.exp (Complex.exp (r : ℂ) - 1)).re
  have harg :
      Complex.exp (r : ℂ) - 1 = ((Real.exp r - 1 : ℝ) : ℂ) := by
    simp
  have hval :
      Complex.exp (Complex.exp (r : ℂ) - 1) =
        ((Real.exp (Real.exp r - 1) : ℝ) : ℂ) := by
    rw [harg]
    simp
  rw [hval]
  exact Real.exp_pos (Real.exp r - 1)

lemma bell_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < bellSaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold bellSaddleBReal
  positivity

lemma bell_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < bellSaddleDeltaReal r :=
  Eventually.of_forall fun r => by
    unfold bellSaddleDeltaReal
    positivity

lemma bell_delta_tendsto_zero :
    Tendsto bellSaddleDeltaReal atTop (𝓝 0) := by
  have hneg : Tendsto (fun r : ℝ => (-(2 / 5 : ℝ)) * r) atTop atBot :=
    Tendsto.const_mul_atTop_of_neg (by norm_num : (-(2 / 5 : ℝ)) < 0) tendsto_id
  change Tendsto (fun r : ℝ => Real.exp ((-(2 / 5 : ℝ)) * r)) atTop (𝓝 0)
  exact Real.tendsto_exp_atBot.comp hneg

lemma bell_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, bellSaddleDeltaReal r ≤ Real.pi :=
  bell_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma bell_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, bellSaddleDeltaReal r ≤ 1 :=
  bell_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma bell_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r))
      atTop atTop := by
  have hexp : Tendsto (fun r : ℝ => Real.exp ((1 / 10 : ℝ) * r)) atTop atTop := by
    have hlin : Tendsto (fun r : ℝ => (1 / 10 : ℝ) * r) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 10) tendsto_id
    exact Real.tendsto_exp_atTop.comp hlin
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hprod_ge_one : 1 ≤ r * (r + 1) := by nlinarith
  have hb_ge_exp : Real.exp r ≤ bellSaddleBReal r := by
    unfold bellSaddleBReal
    calc
      Real.exp r = 1 * Real.exp r := by ring_nf
      _ ≤ (r * (r + 1)) * Real.exp r :=
        mul_le_mul_of_nonneg_right hprod_ge_one (Real.exp_pos r).le
  have hsqrt_ge : Real.exp (r / 2) ≤ Real.sqrt (bellSaddleBReal r) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt hb_ge_exp
  have hδpos : 0 ≤ bellSaddleDeltaReal r := (Real.exp_pos _).le
  calc
    Real.exp ((1 / 10 : ℝ) * r)
        = bellSaddleDeltaReal r * Real.exp (r / 2) := by
          unfold bellSaddleDeltaReal
          rw [← Real.exp_add]
          congr 1
          ring_nf
    _ ≤ bellSaddleDeltaReal r * Real.sqrt (bellSaddleBReal r) :=
          mul_le_mul_of_nonneg_left hsqrt_ge hδpos

lemma bell_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ (fun z : ℂ => Complex.exp (Complex.exp z - 1))
        (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  fun_prop

lemma bellSaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn bellSaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold bellSaddleAReal
  have hexp_le : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy.le
  have h₁ : x * Real.exp x ≤ x * Real.exp y :=
    mul_le_mul_of_nonneg_left hexp_le hx
  have h₂ : x * Real.exp y < y * Real.exp y :=
    mul_lt_mul_of_pos_right hxy (Real.exp_pos y)
  exact lt_of_le_of_lt h₁ h₂

lemma bellSaddleAReal_exists_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ∃ r : ℝ, 0 ≤ r ∧ bellSaddleAReal r = x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · refine ⟨0, by norm_num, ?_⟩
    simp [bellSaddleAReal]
  · have hcont : ContinuousOn bellSaddleAReal (Set.Icc (0 : ℝ) x) := by
      unfold bellSaddleAReal
      fun_prop
    have hleft : bellSaddleAReal 0 ≤ x := by
      simp [bellSaddleAReal, hx]
    have hone_le_exp : 1 ≤ Real.exp x := by
      have h := Real.exp_le_exp.mpr hx
      simpa using h
    have hright : x ≤ bellSaddleAReal x := by
      unfold bellSaddleAReal
      calc
        x = x * 1 := by ring_nf
        _ ≤ x * Real.exp x := mul_le_mul_of_nonneg_left hone_le_exp hx
    have hxI : x ∈ Set.Icc (bellSaddleAReal 0) (bellSaddleAReal x) :=
      ⟨hleft, hright⟩
    rcases intermediate_value_Icc hx hcont hxI with ⟨r, hrmem, hr⟩
    exact ⟨r, hrmem.1, hr⟩

/-- The Bell saddle radius, chosen as the nonnegative solution of `r e^r = n`. -/
noncomputable def bellSaddleRadius (n : ℕ) : ℝ :=
  Classical.choose (bellSaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))

lemma bellSaddleRadius_nonneg (n : ℕ) : 0 ≤ bellSaddleRadius n :=
  (Classical.choose_spec
    (bellSaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).1

lemma bellSaddleAReal_radius (n : ℕ) :
    bellSaddleAReal (bellSaddleRadius n) = (n : ℝ) :=
  (Classical.choose_spec
    (bellSaddleAReal_exists_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)))).2

lemma bellSaddleRadius_tendsto_atTop :
    Tendsto bellSaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (bellSaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : bellSaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : bellSaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : bellSaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      bellSaddleAReal (bellSaddleRadius n) < bellSaddleAReal M0 :=
    bellSaddleAReal_strictMonoOn_nonneg
      (bellSaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [bellSaddleAReal_radius] at hstrict
  linarith

lemma bellLocalExponent_decomp (r θ : ℝ) :
    let w : ℂ := (θ : ℂ) * Complex.I
    let u : ℂ := (r : ℂ) * (Complex.exp w - 1)
    let m : ℂ := (r : ℂ) * w
    bellLocalExponent r θ =
      Complex.exp (r : ℂ) *
        ((Complex.exp u - ∑ k ∈ Finset.range 3, u ^ k / (k.factorial : ℂ)) +
          (r : ℂ) * ExpStirling.expLocalRemainder θ +
            (u ^ 2 - m ^ 2) / 2) := by
  set_option backward.isDefEq.respectTransparency false in
    dsimp
    unfold bellLocalExponent bellSaddleAReal bellSaddleBReal
    rw [show (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) =
        (r : ℂ) + (r : ℂ) * (Complex.exp ((θ : ℂ) * Complex.I) - 1) by ring_nf]
    rw [Complex.exp_add]
    rw [ExpStirling.expLocalRemainder_eq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_succ, pow_zero, pow_one, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_pow]
    norm_num
    rw [show ((r : ℂ) * ((θ : ℂ) * Complex.I)) ^ 2 =
        -((r : ℂ) ^ 2 * (θ : ℂ) ^ 2) by
          rw [mul_pow, mul_pow, Complex.I_sq]
          ring_nf]
    ring_nf

def bellLocalControl (r : ℝ) : ℝ :=
  r ^ 3 * Real.exp (-(1 / 5 : ℝ) * r)

lemma bellLocalControl_tendsto_zero :
    Tendsto bellLocalControl atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun r : ℝ => r ^ (3 : ℝ) * Real.exp (-(1 / 5 : ℝ) * r))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) (1 / 5 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 5)
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold bellLocalControl
  have hpow : r ^ 3 = r ^ (3 : ℝ) := by
    norm_num [Real.rpow_natCast]
  rw [hpow]

lemma bell_r_delta_tendsto_zero :
    Tendsto (fun r : ℝ => r * bellSaddleDeltaReal r) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(2 / 5 : ℝ) * r))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (2 / 5 : ℝ)
      (by norm_num : (0 : ℝ) < 2 / 5)
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold bellSaddleDeltaReal
  rw [Real.rpow_one]

lemma bell_exp_i_sub_one_norm_le_two_abs {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ 2 * |θ| := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_le (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

lemma bell_exp_i_sub_one_sub_id_norm_le_sq {θ : ℝ} (hθ : |θ| ≤ 1) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ |θ| ^ 2 := by
  have hw : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := (θ : ℂ) * Complex.I) (by simpa [hw] using hθ)
  simpa [hw] using h

def bellLocalConstant : ℝ :=
  10 * Real.exp 1 + 4

lemma bellLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => bellLocalConstant * bellLocalControl r) atTop (𝓝 0) := by
  simpa using bellLocalControl_tendsto_zero.const_mul bellLocalConstant

lemma bell_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ bellSaddleDeltaReal r →
      ‖bellLocalExponent r θ‖ ≤ bellLocalConstant * bellLocalControl r := by
  have hsmall_u :
      ∀ᶠ r : ℝ in atTop, 2 * (r * bellSaddleDeltaReal r) ≤ 1 :=
    by
      have ht : Tendsto (fun r : ℝ => 2 * (r * bellSaddleDeltaReal r)) atTop (𝓝 0) := by
        simpa using (bell_r_delta_tendsto_zero.const_mul (2 : ℝ))
      exact ht.eventually_le_const zero_lt_one
  filter_upwards [eventually_ge_atTop (1 : ℝ), bell_delta_le_one_eventually, hsmall_u] with
    r hr hδ_le_one hsmall θ hθδ
  let δ : ℝ := bellSaddleDeltaReal r
  let w : ℂ := (θ : ℂ) * Complex.I
  let u : ℂ := (r : ℂ) * (Complex.exp w - 1)
  let m : ℂ := (r : ℂ) * w
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδpos : 0 ≤ δ := by
    dsimp [δ, bellSaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have hθ2δ2 : |θ| ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ hθ_nonneg hθδ 2
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ hθ_nonneg hθδ 3
  have hu_norm : ‖u‖ ≤ 2 * (r * δ) := by
    have hbase := bell_exp_i_sub_one_norm_le_two_abs hθ_one
    calc
      ‖u‖ = r * ‖Complex.exp w - 1‖ := by
        dsimp [u, w]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (2 * |θ|) := mul_le_mul_of_nonneg_left hbase hr0
      _ ≤ r * (2 * δ) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθδ (by norm_num : (0 : ℝ) ≤ 2)) hr0
      _ = 2 * (r * δ) := by ring_nf
  have hu_le_one : ‖u‖ ≤ 1 := hu_norm.trans hsmall
  have hm_norm : ‖m‖ ≤ r * δ := by
    calc
      ‖m‖ = r * |θ| := by
        dsimp [m, w]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        simp
      _ ≤ r * δ := mul_le_mul_of_nonneg_left hθδ hr0
  have hu_sub_m_norm : ‖u - m‖ ≤ r * δ ^ 2 := by
    have hbase := bell_exp_i_sub_one_sub_id_norm_le_sq hθ_one
    have hdiff :
        u - m = (r : ℂ) *
          (Complex.exp w - 1 - (θ : ℂ) * Complex.I) := by
      dsimp [u, m, w]
      ring_nf
    rw [hdiff]
    calc
      ‖(r : ℂ) * (Complex.exp w - 1 - (θ : ℂ) * Complex.I)‖
          = r * ‖Complex.exp w - 1 - (θ : ℂ) * Complex.I‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * |θ| ^ 2 := mul_le_mul_of_nonneg_left hbase hr0
      _ ≤ r * δ ^ 2 := mul_le_mul_of_nonneg_left hθ2δ2 hr0
  have hu_plus_m_norm : ‖u + m‖ ≤ 3 * (r * δ) := by
    calc
      ‖u + m‖ ≤ ‖u‖ + ‖m‖ := norm_add_le _ _
      _ ≤ 2 * (r * δ) + r * δ := add_le_add hu_norm hm_norm
      _ = 3 * (r * δ) := by ring_nf
  let outer : ℂ := Complex.exp u - ∑ k ∈ Finset.range 3, u ^ k / (k.factorial : ℂ)
  let inner : ℂ := (r : ℂ) * ExpStirling.expLocalRemainder θ
  let cross : ℂ := (u ^ 2 - m ^ 2) / 2
  have houter : ‖outer‖ ≤ Real.exp 1 * (2 * (r * δ)) ^ 3 := by
    have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp u 3
    have hpow : ‖u‖ ^ 3 ≤ (2 * (r * δ)) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg u) hu_norm 3
    have hexp : Real.exp ‖u‖ ≤ Real.exp 1 := Real.exp_le_exp.mpr hu_le_one
    calc
      ‖outer‖ ≤ ‖u‖ ^ 3 * Real.exp ‖u‖ := by
        simpa [outer] using hrem
      _ ≤ (2 * (r * δ)) ^ 3 * Real.exp 1 :=
        mul_le_mul hpow hexp (Real.exp_pos _).le
          (pow_nonneg (by positivity : 0 ≤ 2 * (r * δ)) 3)
      _ = Real.exp 1 * (2 * (r * δ)) ^ 3 := by ring_nf
  have hinner : ‖inner‖ ≤ Real.exp 1 * (r * δ ^ 3) := by
    have hrem := ExpStirling.expLocalRemainder_norm_le_exp_one θ hθ_one
    calc
      ‖inner‖ = r * ‖ExpStirling.expLocalRemainder θ‖ := by
        dsimp [inner]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 1 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem hr0
      _ ≤ r * (Real.exp 1 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 1).le) hr0
      _ = Real.exp 1 * (r * δ ^ 3) := by ring_nf
  have hcross : ‖cross‖ ≤ 2 * (r ^ 2 * δ ^ 3) := by
    have hcross_eq : cross = ((1 / 2 : ℂ) * ((u - m) * (u + m))) := by
      dsimp [cross]
      ring_nf
    rw [hcross_eq]
    rw [norm_mul, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    calc
      (1 / 2 : ℝ) * (‖u - m‖ * ‖u + m‖)
          ≤ (1 / 2 : ℝ) * ((r * δ ^ 2) * (3 * (r * δ))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hu_sub_m_norm hu_plus_m_norm
                (norm_nonneg _) (by positivity : 0 ≤ r * δ ^ 2))
              (by norm_num)
      _ = (3 / 2 : ℝ) * (r ^ 2 * δ ^ 3) := by ring_nf
      _ ≤ 2 * (r ^ 2 * δ ^ 3) :=
        mul_le_mul_of_nonneg_right (by norm_num : (3 / 2 : ℝ) ≤ 2) (by positivity)
  have hsum :
      ‖outer + inner + cross‖ ≤
        (9 * Real.exp 1 + 2) * (r ^ 3 * δ ^ 3) := by
    have houter' : ‖outer‖ ≤ 8 * Real.exp 1 * (r ^ 3 * δ ^ 3) := by
      calc
        ‖outer‖ ≤ Real.exp 1 * (2 * (r * δ)) ^ 3 := houter
        _ = 8 * Real.exp 1 * (r ^ 3 * δ ^ 3) := by ring_nf
    have hinner' : ‖inner‖ ≤ Real.exp 1 * (r ^ 3 * δ ^ 3) := by
      have hr_le_r3 : r * δ ^ 3 ≤ r ^ 3 * δ ^ 3 := by
        have hr_le_r3 : r ≤ r ^ 3 := by nlinarith [hr]
        exact mul_le_mul_of_nonneg_right hr_le_r3 (pow_nonneg hδpos 3)
      exact hinner.trans (mul_le_mul_of_nonneg_left hr_le_r3 (Real.exp_pos 1).le)
    have hcross' : ‖cross‖ ≤ 2 * (r ^ 3 * δ ^ 3) := by
      have hr2_le_r3 : r ^ 2 * δ ^ 3 ≤ r ^ 3 * δ ^ 3 := by
        have hr2_le_r3 : r ^ 2 ≤ r ^ 3 := by nlinarith [hr]
        exact mul_le_mul_of_nonneg_right hr2_le_r3 (pow_nonneg hδpos 3)
      exact hcross.trans (mul_le_mul_of_nonneg_left hr2_le_r3 (by norm_num))
    calc
      ‖outer + inner + cross‖
          ≤ ‖outer‖ + ‖inner‖ + ‖cross‖ := by
            calc
              ‖outer + inner + cross‖ = ‖(outer + inner) + cross‖ := rfl
              _ ≤ ‖outer + inner‖ + ‖cross‖ := norm_add_le _ _
              _ ≤ (‖outer‖ + ‖inner‖) + ‖cross‖ :=
                by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    add_le_add_right (norm_add_le outer inner) ‖cross‖
              _ = ‖outer‖ + ‖inner‖ + ‖cross‖ := by ring_nf
      _ ≤ 8 * Real.exp 1 * (r ^ 3 * δ ^ 3) +
            Real.exp 1 * (r ^ 3 * δ ^ 3) +
              2 * (r ^ 3 * δ ^ 3) := by
            exact add_le_add (add_le_add houter' hinner') hcross'
      _ = (9 * Real.exp 1 + 2) * (r ^ 3 * δ ^ 3) := by ring_nf
  have hdecomp :
      bellLocalExponent r θ = Complex.exp (r : ℂ) * (outer + inner + cross) := by
    simpa [outer, inner, cross, u, m, w] using bellLocalExponent_decomp r θ
  rw [hdecomp]
  rw [norm_mul]
  have hexp_norm : ‖Complex.exp (r : ℂ)‖ = Real.exp r := by simp
  rw [hexp_norm]
  have hmain :
      Real.exp r * ‖outer + inner + cross‖ ≤
        (9 * Real.exp 1 + 2) * (Real.exp r * (r ^ 3 * δ ^ 3)) := by
    calc
      Real.exp r * ‖outer + inner + cross‖
          ≤ Real.exp r * ((9 * Real.exp 1 + 2) * (r ^ 3 * δ ^ 3)) :=
            mul_le_mul_of_nonneg_left hsum (Real.exp_pos r).le
      _ = (9 * Real.exp 1 + 2) * (Real.exp r * (r ^ 3 * δ ^ 3)) := by ring_nf
  refine hmain.trans ?_
  have hconst_le : 9 * Real.exp 1 + 2 ≤ bellLocalConstant := by
    unfold bellLocalConstant
    nlinarith [Real.exp_pos 1]
  have hraw_eq :
      Real.exp r * (r ^ 3 * δ ^ 3) = bellLocalControl r := by
    dsimp [δ, bellSaddleDeltaReal, bellLocalControl]
    have hpowexp :
        (Real.exp (-(2 / 5 : ℝ) * r)) ^ 3 =
          Real.exp (3 * (-(2 / 5 : ℝ) * r)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hpowexp]
    calc
      Real.exp r * (r ^ 3 * Real.exp (3 * (-(2 / 5 : ℝ) * r)))
          = r ^ 3 * (Real.exp r * Real.exp (3 * (-(2 / 5 : ℝ) * r))) := by ring_nf
      _ = r ^ 3 * Real.exp (r + 3 * (-(2 / 5 : ℝ) * r)) := by
        rw [← Real.exp_add]
      _ = r ^ 3 * Real.exp (-(1 / 5 : ℝ) * r) := by
        congr 1
        ring_nf
  rw [hraw_eq]
  exact mul_le_mul_of_nonneg_right hconst_le (by
    unfold bellLocalControl
    positivity)

lemma bell_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ bellSaddleDeltaReal r →
        ‖saddleLocalRatio (fun z : ℂ => Complex.exp (Complex.exp z - 1))
            bellSaddleAReal bellSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, bellLocalConstant * bellLocalControl r ≤ ε / 2 :=
    bellLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, bellLocalConstant * bellLocalControl r ≤ 1 :=
    bellLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [bell_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [bell_saddleLocalRatio_eq]
  have hz : ‖bellLocalExponent r θ‖ ≤ bellLocalConstant * bellLocalControl r :=
    hloc θ hθ
  have hz_one : ‖bellLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (bellLocalExponent r θ) - 1‖
        ≤ 2 * ‖bellLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (bellLocalConstant * bellLocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

def bellTailE (r : ℝ) : ℝ :=
  Real.exp (-r)

lemma bellTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ bellTailE r :=
  Eventually.of_forall fun r => by
    unfold bellTailE
    positivity

lemma bell_saddleGAt_norm_le_exp (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖ ≤
      Real.exp (Real.exp (r * Real.cos θ) - Real.exp r) := by
  unfold saddleGAt
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hfden :
      ‖Complex.exp (Complex.exp (r : ℂ) - 1)‖ =
    Real.exp (Real.exp r - 1) := by
    have hre : (Complex.exp (r : ℂ)).re = Real.exp r := by
      rw [Complex.exp_re]
      simp
    rw [Complex.norm_exp, sub_re, hre]
    simp
  have hnum_re_le :
      (Complex.exp ((r : ℂ) * Complex.exp (θ * Complex.I))).re ≤
        Real.exp (r * Real.cos θ) := by
    have hre : ((r : ℂ) * Complex.exp (θ * Complex.I)).re = r * Real.cos θ := by
      rw [show Complex.exp ((θ : ℂ) * Complex.I) =
          (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I by
            exact Complex.exp_ofReal_mul_I θ]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.exp_re, hre]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.cos_le_one _)
  have hnum :
      ‖Complex.exp (Complex.exp ((r : ℂ) * Complex.exp (θ * Complex.I)) - 1)‖ ≤
        Real.exp (Real.exp (r * Real.cos θ) - 1) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (sub_le_sub_right hnum_re_le 1)
  have hden_pos : 0 < Real.exp (Real.exp r - 1) := Real.exp_pos _
  calc
    ‖Complex.exp (Complex.exp ((r : ℂ) * Complex.exp (↑θ * Complex.I)) - 1) /
          Complex.exp (Complex.exp (↑r) - 1) * Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = ‖Complex.exp (Complex.exp ((r : ℂ) * Complex.exp (↑θ * Complex.I)) - 1)‖ /
            Real.exp (Real.exp r - 1) := by
          rw [norm_mul, hphase, mul_one, norm_div, hfden]
    _ ≤ Real.exp (Real.exp (r * Real.cos θ) - 1) /
          Real.exp (Real.exp r - 1) :=
        div_le_div_of_nonneg_right hnum hden_pos.le
    _ = Real.exp (Real.exp (r * Real.cos θ) - Real.exp r) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

lemma bell_one_sub_exp_neg_ge_half {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    y / 2 ≤ 1 - Real.exp (-y) := by
  have hyabs : |(-y : ℝ)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hy0]
    linarith
  have h := Real.abs_exp_sub_one_sub_id_le (x := -y) hyabs
  have hupper : Real.exp (-y) - 1 + y ≤ y ^ 2 := by
    have hle := (abs_le.mp h).2
    nlinarith
  have hmain : y - y ^ 2 ≤ 1 - Real.exp (-y) := by linarith
  have hyquad : y / 2 ≤ y - y ^ 2 := by
    nlinarith [hy0, hy]
  exact hyquad.trans hmain

lemma bell_tail_y_tendsto_zero :
    Tendsto (fun r : ℝ =>
      (2 / Real.pi ^ 2) * (r * (bellSaddleDeltaReal r) ^ 2)) atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(4 / 5 : ℝ) * r))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (4 / 5 : ℝ)
      (by norm_num : (0 : ℝ) < 4 / 5)
  have hcongr :
      (fun r : ℝ => r * (bellSaddleDeltaReal r) ^ 2) =ᶠ[atTop]
        fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(4 / 5 : ℝ) * r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    unfold bellSaddleDeltaReal
    rw [Real.rpow_one]
    rw [show (Real.exp (-(2 / 5 : ℝ) * r)) ^ 2 =
        Real.exp (2 * (-(2 / 5 : ℝ) * r)) by
          rw [← Real.exp_nat_mul]
          norm_num]
    congr 1
    ring_nf
  have ht : Tendsto (fun r : ℝ => r * (bellSaddleDeltaReal r) ^ 2) atTop (𝓝 0) :=
    Tendsto.congr' hcongr.symm hbase
  simpa using ht.const_mul (2 / Real.pi ^ 2)

lemma bell_exp_one_fifth_tendsto_atTop :
    Tendsto (fun r : ℝ => Real.exp ((1 / 5 : ℝ) * r)) atTop atTop := by
  have hlin : Tendsto (fun r : ℝ => (1 / 5 : ℝ) * r) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 5) tendsto_id
  exact Real.tendsto_exp_atTop.comp hlin

lemma bell_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      bellSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖ ≤ bellTailE r := by
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
    have hexp_big :
        ∀ᶠ r : ℝ in atTop, Real.pi ^ 2 ≤ Real.exp ((1 / 5 : ℝ) * r) :=
      bell_exp_one_fifth_tendsto_atTop.eventually_ge_atTop (Real.pi ^ 2)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hy_small, hexp_big] with
      r hr hy_small_r hexp_big_r n θ hδθ hθπ
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
    have hle_neg_r :
        Real.exp (r * Real.cos θ) - Real.exp r ≤ -r := by
      have hcoef : 1 ≤ (1 / Real.pi ^ 2) * Real.exp ((1 / 5 : ℝ) * r) := by
        have hpi_pos : 0 < Real.pi ^ 2 := by positivity
        have hdiv :
            Real.pi ^ 2 / Real.pi ^ 2 ≤
              Real.exp ((1 / 5 : ℝ) * r) / Real.pi ^ 2 :=
          div_le_div_of_nonneg_right hexp_big_r hpi_pos.le
        calc
          1 = Real.pi ^ 2 / Real.pi ^ 2 := by field_simp [hpi_pos.ne']
          _ ≤ Real.exp ((1 / 5 : ℝ) * r) / Real.pi ^ 2 := hdiv
          _ = (1 / Real.pi ^ 2) * Real.exp ((1 / 5 : ℝ) * r) := by ring_nf
      have hmul : r ≤ (1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r) := by
        calc
          r = r * 1 := by ring_nf
          _ ≤ r * ((1 / Real.pi ^ 2) * Real.exp ((1 / 5 : ℝ) * r)) :=
            mul_le_mul_of_nonneg_left hcoef hr0
          _ = (1 / Real.pi ^ 2) * r * Real.exp ((1 / 5 : ℝ) * r) := by ring_nf
      linarith
    calc
      ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖
          ≤ Real.exp (Real.exp (r * Real.cos θ) - Real.exp r) :=
            bell_saddleGAt_norm_le_exp r n θ
      _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr hle_neg_r
      _ = bellTailE r := by rfl

/- The remaining analytic tail decay field is below. -/

lemma bellTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellTailE r)
      atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(1 / 2 : ℝ) * r))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hscaled :
      Tendsto (fun r : ℝ =>
        Real.sqrt (4 * Real.pi) * (r * Real.exp (-(1 / 2 : ℝ) * r)))
        atTop (𝓝 0) := by
    simpa [Real.rpow_one] using hbase.const_mul (Real.sqrt (4 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
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
    calc
      Real.sqrt (2 * Real.pi * bellSaddleBReal r) * bellTailE r
          ≤ (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2))) * bellTailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold bellTailE
              positivity)
      _ = Real.sqrt (4 * Real.pi) * (r * Real.exp (-(1 / 2 : ℝ) * r)) := by
        unfold bellTailE
        calc
          (Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2))) * Real.exp (-r)
              = Real.sqrt (4 * Real.pi) * (r *
                  (Real.exp (r / 2) * Real.exp (-r))) := by ring_nf
          _ = Real.sqrt (4 * Real.pi) * (r * Real.exp (r / 2 + -r)) := by
            rw [← Real.exp_add]
          _ = Real.sqrt (4 * Real.pi) *
                (r * Real.exp (-(1 / 2 : ℝ) * r)) := by
            congr 2
            ring_nf

lemma bell_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * bellSaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        bellSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt (fun z : ℂ => Complex.exp (Complex.exp z - 1)) r n θ‖ ≤ E r) := by
  exact ⟨bellTailE, bellTailE_nonneg_eventually, bellTailE_decay, bell_tail_bound_eventually⟩

def bellHAdmissible :
    HAdmissible (fun z : ℂ => Complex.exp (Complex.exp z - 1)) bellSeries where
  ρ := bellSeries.radius
  radFilter := atTop
  a := bellSaddleAReal
  b := bellSaddleBReal
  δ := bellSaddleDeltaReal
  hp := by
    simpa [bellSeries, analyticBellFun] using analyticBell_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [bellSeries] using analyticBell_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := bell_differentiableOn_eventually
  f_pos := bell_f_pos_eventually
  b_pos := bell_b_pos_eventually
  δ_pos := bell_delta_pos_eventually
  δ_le_pi := bell_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := bell_delta_sqrt_b_tendsto_atTop
  local_uniform := bell_local_uniform
  tail_uniform := bell_tail_uniform

def bellHAdmissibleSaddleSequence : SaddleSequence bellHAdmissible where
  r := bellSaddleRadius
  tendsTo := by
    simpa [bellHAdmissible] using bellSaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change bellSaddleAReal (bellSaddleRadius n) = (n : ℝ)
      exact bellSaddleAReal_radius n


