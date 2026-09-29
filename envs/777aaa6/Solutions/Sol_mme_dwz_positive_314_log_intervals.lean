-- Prove2me | solution 1 for mme_dwz_positive_314_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T15:32:52.244298+00:00
-- url     : https://prove2.me/submissions/f3a340d5-2c0f-4abc-8280-54c985471ad6

import Definitions.Def_mme_dwz_positive_314_entropy_certificate_data

open BigOperators Finset MME.DWZ314Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem valid_all : ∀ j, Valid (certificates j) := by
  decide +kernel

theorem solution : ∀ j : Fin 142,
    ((certificates j).lo : ℝ) ≤ Real.log ((certificates j).q : ℝ) ∧
    Real.log ((certificates j).q : ℝ) ≤ ((certificates j).hi : ℝ) := by
  intro j
  obtain ⟨hq,ht0,ht1,hscale,hlo,hhi⟩ := valid_all j
  exact mme_log_interval_of_exact_rational_series_certificate
    _ _ _ _ _ _ hq ht0 ht1 hscale hlo hhi
