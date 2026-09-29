-- Prove2me | solution 1 for mme_dwz_positive_611_log_intervals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T18:23:30.975088+00:00
-- url     : https://prove2.me/submissions/689bbef5-4bab-4173-8a8d-7602be7debfe

import Definitions.Def_mme_dwz_positive_611_entropy_certificate_data

open BigOperators Finset MME.DWZ611Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem valid_all : ∀ j, Valid (certificates j) := by
  decide +kernel

theorem solution : ∀ j : Fin 45,
    ((certificates j).lo : ℝ) ≤ Real.log ((certificates j).q : ℝ) ∧
    Real.log ((certificates j).q : ℝ) ≤ ((certificates j).hi : ℝ) := by
  intro j
  obtain ⟨hq,ht0,ht1,hscale,hlo,hhi⟩ := valid_all j
  exact mme_log_interval_of_exact_rational_series_certificate
    _ _ _ _ _ _ hq ht0 ht1 hscale hlo hhi
