-- Prove2me | solution 1 for mme_released_global_x_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:56:46.309744+00:00
-- url     : https://prove2.me/submissions/f51dd0d5-04f6-461f-9ea4-b111296f7f69

import Definitions.Def_mme_released_global_x_certificate
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
open BigOperators MME MME.ReleasedGlobalNumeric
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

private theorem certified : ∀ o j,
    0 < xInputs o j ∧ 1 ≤ xInputs o j * 2^xShift o j ∧
    xLogLower o j ≤ autoScaledLogLower (xInputs o j) (xShift o j) 12 ∧
    autoScaledLogUpper (xInputs o j) (xShift o j) 12 ≤ xLogUpper o j := by
  decide +kernel

theorem solution (o : Fin 6) (j : Fin 99) :
    (xLogLower o j : ℝ) ≤ Real.log (xInputs o j : ℝ) ∧
    Real.log (xInputs o j : ℝ) ≤ (xLogUpper o j : ℝ) := by
  have h := certified o j
  have hl := mme_log_interval_of_auto_scaled_rational (xInputs o j) (xShift o j) 12 h.1 h.2.1
  constructor
  · have hb : (xLogLower o j : ℝ) ≤ (autoScaledLogLower (xInputs o j) (xShift o j) 12 : ℝ) := by exact_mod_cast h.2.2.1
    exact hb.trans hl.1
  · exact hl.2.trans (by exact_mod_cast h.2.2.2)
