-- Prove2me | solution 1 for mme_more_asymmetry_released_witness_finite_loss_reserve
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T20:08:26.860278+00:00
-- url     : https://prove2.me/submissions/f579f236-3d81-4326-bd5e-e81f1523910b

import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
import Mathlib
open MME
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution :
    4 * Real.log 7 + (8 : ℝ) / 10000000 <
      ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
      ((3952233 : ℝ) / 5000000) *
        (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) := by
  have h := (mme_log_interval_of_auto_scaled_rational 7 0 50
    (by norm_num) (by norm_num)).2
  have hc : autoScaledLogUpper 7 0 50 ≤ (194591014906 / 100000000000 : ℚ) := by
    decide +kernel
  have hc' : (autoScaledLogUpper 7 0 50 : ℝ) ≤
      ((194591014906 / 100000000000 : ℚ) : ℝ) := Rat.cast_le.mpr hc
  push_cast at hc'
  norm_num at h
  linarith
