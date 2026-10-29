-- Prove2me | solution 1 for RybinAI2026.P01.psi_large_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:36:26.181712+00:00
-- url     : https://prove2.me/submissions/d83675f2-727f-4adc-a555-8ddaf36c8cc6

import Mathlib

open MeasureTheory

theorem solution {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∫ s in (0 : ℝ)..1, (1 + ((1 / b) - 1) * s ^ 2)⁻¹) ≤ 2 / Real.sqrt ((1 / b) - 1) := by
  have hc : 0 < (1 / b) - 1 := by
    rw [sub_pos, lt_div_iff₀ hb]; linarith
  set c := (1 / b) - 1 with hcdef
  set r := Real.sqrt c with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hc
  have hr2 : r ^ 2 = c := Real.sq_sqrt hc.le
  have hfun : (fun s : ℝ => (1 + c * s ^ 2)⁻¹) = fun s => (1 + (r * s) ^ 2)⁻¹ := by
    funext s; rw [mul_pow, hr2]
  have hint : (∫ s in (0 : ℝ)..1, (1 + c * s ^ 2)⁻¹) = Real.arctan r / r := by
    rw [hfun, intervalIntegral.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) hr.ne',
      integral_inv_one_add_sq, mul_zero, mul_one, Real.arctan_zero, sub_zero, smul_eq_mul]
    field_simp
  rw [hint]
  apply div_le_div_of_nonneg_right _ hr.le
  have := Real.arctan_lt_pi_div_two r
  linarith [Real.pi_lt_four]
