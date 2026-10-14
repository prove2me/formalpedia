-- Prove2me | solution 1 for CatalanLogSin.integral_log_one_sub_inv_four_cos_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T19:32:32.952203+00:00
-- url     : https://prove2.me/submissions/18a3916b-4398-482e-9b3f-31065cee02d5

import Mathlib
import Theorems.Thm_CatalanLogSin_integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three

theorem solution :
    ∫ θ in (0:ℝ)..Real.pi / 4, Real.log (1 - 1 / (4 * Real.cos θ ^ 2))
      = -((∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) / 3) :=
  CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three
