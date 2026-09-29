-- Prove2me | solution 1 for mme_dwz_fourth_terminal_log_margin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T04:56:48.426043+00:00
-- url     : https://prove2.me/submissions/6c446a01-8378-4de3-b622-adf6f1b8c929

import Definitions.Def_mme_dwz_fourth_terminal_log_margin_data
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate

open MME MME.DWZFourthScalar
open BigOperators Finset
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthScalar

private theorem reciprocal_five_log_interval :
    (reciprocalFiveLogLower : ℝ) ≤ Real.log (1 / 5 : ℝ) ∧
      Real.log (1 / 5 : ℝ) ≤ (reciprocalFiveLogUpper : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
      (1 / 5) reciprocalFiveT reciprocalFiveLogLower
      reciprocalFiveLogUpper 3 6
      (by norm_num)
      (by norm_num [reciprocalFiveT])
      (by norm_num [reciprocalFiveT])
      (by norm_num [reciprocalFiveT])
      (by norm_num [reciprocalFiveT, reciprocalFiveLogLower])
      (by norm_num [reciprocalFiveT, reciprocalFiveLogUpper])
  simpa using h

private theorem log_five_lower : (logFiveLower : ℝ) ≤ Real.log 5 := by
  have h := reciprocal_five_log_interval.2
  rw [show (1 / 5 : ℝ) = (5 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  simpa [logFiveLower] using neg_le_neg h

private theorem reciprocal_target_log_interval :
    (reciprocalTargetLogLower : ℝ) ≤ Real.log (100 / 240101 : ℝ) ∧
      Real.log (100 / 240101 : ℝ) ≤
        (reciprocalTargetLogUpper : ℝ) := by
  have h := mme_log_interval_of_exact_rational_series_certificate
      (100 / 240101) reciprocalTargetT reciprocalTargetLogLower
      reciprocalTargetLogUpper 12 6
      (by norm_num)
      (by norm_num [reciprocalTargetT])
      (by norm_num [reciprocalTargetT])
      (by norm_num [reciprocalTargetT])
      (by norm_num [reciprocalTargetT, reciprocalTargetLogLower])
      (by norm_num [reciprocalTargetT, reciprocalTargetLogUpper])
  simpa using h

private theorem target_log_upper :
    Real.log (240101 / 100 : ℝ) ≤ (targetLogUpper : ℝ) := by
  have h := reciprocal_target_log_interval.1
  have hinv : (240101 / 100 : ℝ) = (100 / 240101 : ℝ)⁻¹ := by
    norm_num
  rw [hinv, Real.log_inv]
  simpa [targetLogUpper] using neg_le_neg h

private theorem exact_terminal_log_margin : targetLogUpper < naturalRateFloor := by
  norm_num [targetLogUpper, naturalRateFloor, reciprocalTargetLogLower,
    reciprocalTargetT]

/- Thus the complete recursive scalar assembly only has to clear the rational
   floor 7.78365 in natural-log units; the terminal comparison is already exact. -/
private theorem fourth_value_exceeds_2401_01_of_natural_rate_floor
    (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate) :
    (240101 / 100 : ℝ) < Real.exp naturalRate := by
  have hlog : Real.log (240101 / 100 : ℝ) < naturalRate :=
    lt_of_le_of_lt target_log_upper
      (lt_of_lt_of_le (by exact_mod_cast exact_terminal_log_margin) hRate)
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 240101 / 100)]
  exact Real.exp_lt_exp.mpr hlog

end MME.DWZFourthScalar

theorem solution :
    ∀ (naturalRate : ℝ) (hRate : (naturalRateFloor : ℝ) ≤ naturalRate),
    (240101 / 100 : ℝ) < Real.exp naturalRate :=
  fourth_value_exceeds_2401_01_of_natural_rate_floor
