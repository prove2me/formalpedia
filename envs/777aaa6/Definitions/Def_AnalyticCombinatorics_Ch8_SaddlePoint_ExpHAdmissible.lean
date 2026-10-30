-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:14:26.994889+00:00
-- url     : https://prove2.me/theorems/92463aa9-861e-4597-a00d-222306e35db5
-- title:
--   Concrete exponential admissibility data
-- statement:
--   The continuous exponential saddle functions are a(r)=b(r)=r and delta(r)=r^(-2/5). A quadratic exponential Taylor remainder and an explicit decaying tail function supply the closed admissibility record, with the natural-radius saddle sequence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/ExpHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# The exponential H-admissible instance

This file packages the concrete Hayman/H-admissible data for `f z = exp z`.
The saddle data are the continuous-radius versions of the quantities used in
`ExpStirling`: `a r = r`, `b r = r`, and `δ r = r^(-2/5)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

def expSaddleAReal (r : ℝ) : ℝ := r

def expSaddleBReal (r : ℝ) : ℝ := r

def expSaddleDeltaReal (r : ℝ) : ℝ := r ^ (-(2 / 5 : ℝ))

@[simp] lemma expSaddleAReal_apply (r : ℝ) : expSaddleAReal r = r := rfl

@[simp] lemma expSaddleBReal_apply (r : ℝ) : expSaddleBReal r = r := rfl

@[simp] lemma expSaddleDeltaReal_apply (r : ℝ) :
    expSaddleDeltaReal r = r ^ (-(2 / 5 : ℝ)) := rfl

def expLocalRemainder (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I) -
    ∑ m ∈ Finset.range 3, (((θ : ℂ) * Complex.I) ^ m) / (m.factorial : ℂ)

lemma expLocalRemainder_eq (θ : ℝ) :
    expLocalRemainder θ =
      Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I +
        ((θ ^ 2 / 2 : ℝ) : ℂ) := by
  simp [expLocalRemainder, Finset.sum_range_succ, pow_two]
  have hsq :
      (θ : ℂ) * Complex.I * ((θ : ℂ) * Complex.I) =
        -((θ : ℂ) * (θ : ℂ)) := by
    rw [show (θ : ℂ) * Complex.I * ((θ : ℂ) * Complex.I) =
        (θ : ℂ) * (θ : ℂ) * (Complex.I * Complex.I) by ring]
    simp
  rw [hsq]
  ring

lemma expLocalRemainder_norm_le (θ : ℝ) :
    ‖expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((θ : ℂ) * Complex.I) 3
  have hnorm : ‖(θ : ℂ) * Complex.I‖ = |θ| := by
    simp
  simpa [expLocalRemainder, hnorm] using h

lemma expLocalRemainder_norm_le_exp_one (θ : ℝ) (hθ : |θ| ≤ 1) :
    ‖expLocalRemainder θ‖ ≤ Real.exp 1 * |θ| ^ 3 := by
  calc
    ‖expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 1 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 1 * |θ| ^ 3 := by ring

lemma exp_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio Complex.exp expSaddleAReal expSaddleBReal r θ =
      Complex.exp ((r : ℂ) * expLocalRemainder θ) := by
  unfold saddleLocalRatio expSaddleAReal expSaddleBReal
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [expLocalRemainder_eq]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow]
  ring

lemma expLocalScale_eq_rpow_eventually :
    (fun r : ℝ => r * (r ^ (-(2 / 5 : ℝ))) ^ 3) =ᶠ[atTop]
      fun r : ℝ => r ^ (-(1 / 5 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hnonneg : 0 ≤ r := hr.le
  calc
    r * (r ^ (-(2 / 5 : ℝ))) ^ 3
        = r ^ (1 : ℝ) * r ^ (-(2 / 5 : ℝ) * (3 : ℝ)) := by
          rw [Real.rpow_one]
          rw [← Real.rpow_mul_natCast hnonneg (-(2 / 5 : ℝ)) 3]
          norm_num
    _ = r ^ ((1 : ℝ) + (-(2 / 5 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 5 : ℝ)) := by norm_num

lemma expLocalScale_tendsto_zero :
    Tendsto (fun r : ℝ => r * (r ^ (-(2 / 5 : ℝ))) ^ 3) atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 5 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
  exact Tendsto.congr' expLocalScale_eq_rpow_eventually.symm hpow

lemma expLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => Real.exp 1 *
      (r * (r ^ (-(2 / 5 : ℝ))) ^ 3)) atTop (𝓝 0) := by
  simpa using expLocalScale_tendsto_zero.const_mul (Real.exp 1)

lemma exp_local_exponent_norm_le
    {r θ : ℝ} (hr : 1 ≤ r) (hθ : |θ| ≤ expSaddleDeltaReal r) :
    ‖(r : ℂ) * expLocalRemainder θ‖ ≤
      Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3) := by
  have hδ_le_one : expSaddleDeltaReal r ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num : (-(2 / 5 : ℝ)) ≤ 0)
  have hθ_one : |θ| ≤ 1 := hθ.trans hδ_le_one
  have hrem := expLocalRemainder_norm_le_exp_one θ hθ_one
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr
  have hθ_nonneg : 0 ≤ |θ| := abs_nonneg θ
  have hδ_nonneg : 0 ≤ expSaddleDeltaReal r := Real.rpow_nonneg hr_nonneg _
  have hθ_cubed : |θ| ^ 3 ≤ (expSaddleDeltaReal r) ^ 3 :=
    pow_le_pow_left₀ hθ_nonneg hθ 3
  calc
    ‖(r : ℂ) * expLocalRemainder θ‖
        = r * ‖expLocalRemainder θ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    _ ≤ r * (Real.exp 1 * |θ| ^ 3) :=
          mul_le_mul_of_nonneg_left hrem hr_nonneg
    _ ≤ r * (Real.exp 1 * (expSaddleDeltaReal r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hθ_cubed (Real.exp_pos 1).le) hr_nonneg
    _ = Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3) := by
          simp [expSaddleDeltaReal]
          ring

lemma exp_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ expSaddleDeltaReal r →
        ‖saddleLocalRatio Complex.exp expSaddleAReal expSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop,
        Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3) ≤ ε / 2 :=
    expLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop,
        Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3) ≤ 1 :=
    expLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall, hone] with r hr hsmallr honer θ hθ
  rw [exp_saddleLocalRatio_eq]
  have hz :
      ‖(r : ℂ) * expLocalRemainder θ‖ ≤
        Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3) :=
    exp_local_exponent_norm_le hr hθ
  have hz_one : ‖(r : ℂ) * expLocalRemainder θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp ((r : ℂ) * expLocalRemainder θ) - 1‖
        ≤ 2 * ‖(r : ℂ) * expLocalRemainder θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (Real.exp 1 * (r * (r ^ (-(2 / 5 : ℝ))) ^ 3)) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma expDeltaReal_mul_sqrt_eq_rpow_eventually :
    (fun r : ℝ => expSaddleDeltaReal r * Real.sqrt (expSaddleBReal r)) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 10 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hnonneg : 0 ≤ r := hr.le
  calc
    expSaddleDeltaReal r * Real.sqrt (expSaddleBReal r)
        = r ^ (-(2 / 5 : ℝ)) * r ^ (1 / 2 : ℝ) := by
          simp [expSaddleDeltaReal, expSaddleBReal, Real.sqrt_eq_rpow]
    _ = r ^ (-(2 / 5 : ℝ) + (1 / 2 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 10 : ℝ) := by norm_num

lemma expDeltaReal_mul_sqrt_tendsto_atTop :
    Tendsto (fun r : ℝ => expSaddleDeltaReal r * Real.sqrt (expSaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 10 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)
  exact Tendsto.congr' expDeltaReal_mul_sqrt_eq_rpow_eventually.symm hpow

lemma expDeltaReal_tendsto_zero :
    Tendsto expSaddleDeltaReal atTop (𝓝 0) := by
  simpa [expSaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))

lemma expDeltaReal_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, expSaddleDeltaReal r ≤ Real.pi :=
  expDeltaReal_tendsto_zero.eventually_le_const Real.pi_pos

lemma exp_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt Complex.exp r n θ‖ =
      Real.exp (r * (Real.cos θ - 1)) := by
  simp [saddleGAt, Complex.norm_exp, Complex.exp_re]
  rw [← Real.exp_sub]
  congr 1
  ring

def expTailE (r : ℝ) : ℝ :=
  Real.exp (-(2 / Real.pi ^ 2) * (r ^ (1 / 5 : ℝ)))

lemma expTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ expTailE r :=
  Eventually.of_forall fun _ => (Real.exp_pos _).le

lemma expTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * expSaddleBReal r) * expTailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 2 / Real.pi ^ 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hy : Tendsto (fun r : ℝ => r ^ (1 / 5 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)
  have hbase : Tendsto (fun y : ℝ => y ^ (5 / 2 : ℝ) * Real.exp (-c * y)) atTop
      (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) c hc
  have hcomp : Tendsto
      (fun r : ℝ => (r ^ (1 / 5 : ℝ)) ^ (5 / 2 : ℝ) *
        Real.exp (-c * (r ^ (1 / 5 : ℝ)))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled : Tendsto
      (fun r : ℝ => Real.sqrt (2 * Real.pi) *
        ((r ^ (1 / 5 : ℝ)) ^ (5 / 2 : ℝ) *
          Real.exp (-c * (r ^ (1 / 5 : ℝ))))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (2 * Real.pi))
  refine Tendsto.congr' ?_ hscaled
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hnonneg : 0 ≤ r := hr.le
  have h2pi_nonneg : 0 ≤ 2 * Real.pi := by positivity
  have hrpow : (r ^ (1 / 5 : ℝ)) ^ (5 / 2 : ℝ) = Real.sqrt r := by
    rw [← Real.rpow_mul hnonneg]
    norm_num
    rw [Real.sqrt_eq_rpow r]
  rw [hrpow]
  dsimp [expTailE, expSaddleBReal, c]
  rw [Real.sqrt_mul h2pi_nonneg r]
  ring

lemma exp_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      expSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt Complex.exp r n θ‖ ≤ expTailE r := by
  let c : ℝ := 2 / Real.pi ^ 2
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr n θ hδθ hθπ
  rw [exp_saddleGAt_norm]
  unfold expTailE
  apply Real.exp_le_exp.mpr
  have hr_nonneg : 0 ≤ r := hr.le
  have hδ_nonneg : 0 ≤ expSaddleDeltaReal r := Real.rpow_nonneg hr_nonneg _
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθπ
  have hcos_sub : Real.cos θ - 1 ≤ -c * θ ^ 2 := by
    dsimp [c] at hcos ⊢
    linarith
  have hθsq : (expSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
    calc
      (expSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
        pow_le_pow_left₀ hδ_nonneg hδθ 2
      _ = θ ^ 2 := by rw [sq_abs]
  have hcoef_nonpos : -c ≤ 0 := by linarith
  have hsquare_bound :
      -c * θ ^ 2 ≤ -c * (expSaddleDeltaReal r) ^ 2 :=
    mul_le_mul_of_nonpos_left hθsq hcoef_nonpos
  have htailScale :
      r * (expSaddleDeltaReal r) ^ 2 = r ^ (1 / 5 : ℝ) := by
    have hnonneg : 0 ≤ r := hr.le
    calc
      r * (expSaddleDeltaReal r) ^ 2
          = r ^ (1 : ℝ) * r ^ (-(2 / 5 : ℝ) * (2 : ℝ)) := by
            rw [Real.rpow_one]
            unfold expSaddleDeltaReal
            rw [← Real.rpow_mul_natCast hnonneg (-(2 / 5 : ℝ)) 2]
            norm_num
      _ = r ^ ((1 : ℝ) + (-(2 / 5 : ℝ) * (2 : ℝ))) := by
            rw [Real.rpow_add hr]
      _ = r ^ (1 / 5 : ℝ) := by norm_num
  calc
    r * (Real.cos θ - 1)
        ≤ r * (-c * θ ^ 2) :=
          mul_le_mul_of_nonneg_left hcos_sub hr_nonneg
    _ ≤ r * (-c * (expSaddleDeltaReal r) ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare_bound hr_nonneg
    _ = -c * (r * (expSaddleDeltaReal r) ^ 2) := by ring
    _ = -(2 / Real.pi ^ 2) * r ^ (1 / 5 : ℝ) := by
          rw [htailScale]

lemma exp_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * expSaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        expSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt Complex.exp r n θ‖ ≤ E r) := by
  exact ⟨expTailE, expTailE_nonneg_eventually, expTailE_decay, exp_tail_bound_eventually⟩

def expHAdmissible : HAdmissible Complex.exp expSeriesC where
  ρ := ⊤
  radFilter := atTop
  a := expSaddleAReal
  b := expSaddleBReal
  δ := expSaddleDeltaReal
  hp := exp_hasFPowerSeriesAt_zero
  radius_eq := by
    simp [expSeriesC, NormedSpace.expSeries_radius_eq_top]
  radius_pos := by
    simp
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn :=
    Eventually.of_forall fun _ => Complex.differentiable_exp.differentiableOn
  f_pos := by
    refine Eventually.of_forall fun r => ?_
    simpa using Real.exp_pos r
  b_pos := by
    simpa [expSaddleBReal] using eventually_gt_atTop (0 : ℝ)
  δ_pos := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact Real.rpow_pos_of_pos hr _
  δ_le_pi := expDeltaReal_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := expDeltaReal_mul_sqrt_tendsto_atTop
  local_uniform := exp_local_uniform
  tail_uniform := exp_tail_uniform

def expHAdmissibleSaddleSequence : SaddleSequence expHAdmissible where
  r := expSaddleRadius
  tendsTo := by
    simpa [expSaddleRadius, expHAdmissible] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      simp [expHAdmissible, expSaddleAReal, expSaddleRadius]

end ExpStirling


