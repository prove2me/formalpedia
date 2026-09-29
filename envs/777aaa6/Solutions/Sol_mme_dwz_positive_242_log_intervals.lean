-- Prove2me | solution 1 for mme_dwz_positive_242_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T16:59:00.013987+00:00
-- url     : https://prove2.me/submissions/bf60d060-cf68-45df-a5a5-9a4a3e1cffe1

import Definitions.Def_mme_dwz_positive_242_entropy_certificate_data

open BigOperators Finset MME.DWZ242Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem valid_all : ∀ j, Valid (certificates j) := by
  decide +kernel

theorem solution : ∀ j : Fin 212,
    ((certificates j).lo : ℝ) ≤ Real.log ((certificates j).q : ℝ) ∧
    Real.log ((certificates j).q : ℝ) ≤ ((certificates j).hi : ℝ) := by
  intro j
  obtain ⟨hq,ht0,ht1,hscale,hlo,hhi⟩ := valid_all j
  exact mme_log_interval_of_exact_rational_series_certificate
    _ _ _ _ _ _ hq ht0 ht1 hscale hlo hhi
