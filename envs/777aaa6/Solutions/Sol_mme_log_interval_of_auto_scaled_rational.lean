-- Prove2me | solution 1 for mme_log_interval_of_auto_scaled_rational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T15:00:44.015045+00:00
-- url     : https://prove2.me/submissions/e1720af1-9b81-45eb-920e-303217338016

import Definitions.Def_mme_auto_scaled_log_interval_data
import Mathlib.Tactic
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate

open MME BigOperators Finset

set_option autoImplicit false

/-- A scale table only has to prove positivity and that the scaled argument is
at least one.  The logarithm interval endpoints are then computed, not stored
as independent certificate fields. -/
theorem solution
    (q : ℚ) (k n : ℕ) (hq : 0 < q) (hscaleLower : 1 ≤ q * 2 ^ k) :
    (autoScaledLogLower q k n : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (autoScaledLogUpper q k n : ℝ) := by
  let x : ℚ := q * 2 ^ k
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hscaleLower
  have hxp : 0 < x + 1 := by linarith
  have ht0 : 0 ≤ (x - 1) / (x + 1) :=
    div_nonneg (sub_nonneg.mpr hscaleLower) hxp.le
  have ht1 : (x - 1) / (x + 1) < 1 := by
    rw [div_lt_one hxp]
    linarith
  apply mme_log_interval_of_exact_rational_series_certificate
      q (autoScaledLogParameter q k)
      (autoScaledLogLower q k n) (autoScaledLogUpper q k n) k n hq
  · simpa [autoScaledLogParameter, x] using ht0
  · simpa [autoScaledLogParameter, x] using ht1
  · dsimp [autoScaledLogParameter, x]
    field_simp
    ring
  · simp [autoScaledLogLower, autoScaledLogPartial]
  · simp [autoScaledLogUpper, autoScaledLogPartial]
