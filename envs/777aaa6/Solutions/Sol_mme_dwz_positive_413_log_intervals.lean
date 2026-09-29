-- Prove2me | solution 1 for mme_dwz_positive_413_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T15:32:20.714476+00:00
-- url     : https://prove2.me/submissions/6e2ee0ab-7f52-46d1-a5d9-ec521725e541

import Definitions.Def_mme_dwz_positive_413_entropy_certificate_data

open BigOperators Finset MME.DWZ413Certificate
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
