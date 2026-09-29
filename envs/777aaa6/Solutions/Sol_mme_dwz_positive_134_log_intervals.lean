-- Prove2me | solution 1 for mme_dwz_positive_134_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-20T19:52:40.984454+00:00
-- url     : https://prove2.me/submissions/d87d5a26-8f83-4c95-a426-491cf7b96886

import Definitions.Def_mme_dwz_positive_134_entropy_certificate_data

open BigOperators Finset MME.DWZ134Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem valid_all : ∀ j, Valid (certificates j) := by
  decide +kernel

theorem solution : ∀ j : Fin 134,
    ((certificates j).lo : ℝ) ≤ Real.log ((certificates j).q : ℝ) ∧
    Real.log ((certificates j).q : ℝ) ≤ ((certificates j).hi : ℝ) := by
  intro j
  obtain ⟨hq,ht0,ht1,hscale,hlo,hhi⟩ := valid_all j
  exact mme_log_interval_of_exact_rational_series_certificate
    _ _ _ _ _ _ hq ht0 ht1 hscale hlo hhi
