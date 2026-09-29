-- Prove2me | solution 1 for mme_released_global_yz_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T13:23:26.799091+00:00
-- url     : https://prove2.me/submissions/658ebf0c-0d3a-4781-9c1b-b4092e85fbbf

import Definitions.Def_mme_released_global_yz_certificate
import Theorems.Thm_mme_log_interval_of_auto_scaled_rational
open BigOperators MME MME.ReleasedGlobalYZ
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

private theorem certified : ∀ o i, ∀ e ∈ entries o i,
    0 < e.1.2 ∧ 1 ≤ e.1.2 * 2^e.2.1 ∧
    e.2.2.1 ≤ autoScaledLogLower e.1.2 e.2.1 12 ∧
    autoScaledLogUpper e.1.2 e.2.1 12 ≤ e.2.2.2 := by
  intro o i
  fin_cases o <;> fin_cases i <;> decide +kernel

theorem solution (o : Fin 6) (i : Fin 2) (e : Entry) (he : e ∈ entries o i) :
    (e.2.2.1 : ℝ) ≤ Real.log (e.1.2 : ℝ) ∧
      Real.log (e.1.2 : ℝ) ≤ (e.2.2.2 : ℝ) := by
  have h := certified o i e he
  have hl := mme_log_interval_of_auto_scaled_rational e.1.2 e.2.1 12 h.1 h.2.1
  constructor
  · have hb : (e.2.2.1 : ℝ) ≤ (autoScaledLogLower e.1.2 e.2.1 12 : ℝ) := by exact_mod_cast h.2.2.1
    exact hb.trans hl.1
  · have hb : (autoScaledLogUpper e.1.2 e.2.1 12 : ℝ) ≤ (e.2.2.2 : ℝ) := by exact_mod_cast h.2.2.2
    exact hl.2.trans hb
