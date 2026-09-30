-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_log_slope_bound_of_ode
-- name    : RybinAI2026.P01.psi_log_slope_bound_of_ode
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:55:44.765082+00:00
-- url     : https://prove2.me/theorems/178c46b9-9bb8-40a1-a1d3-3c3b8c192fee
-- title:
--   The psi differential identity implies the slope envelope
-- statement:
--   If a positive scalar function value and derivative satisfy the differential identity obtained by integration by parts, the two square-root comparison bounds imply the logarithmic-slope envelope for sqrt(t)*psi(t). At t=1, the explicit derivative bound handles the removable limit.
-- source:
--   Scalar calculus connector between the psi integration-by-parts identity and the slope envelope in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_eta_envelope_of_sqrt_comparison

theorem RybinAI2026.P01.psi_log_slope_bound_of_ode (t ψ ψ' : ℝ)
    (ht : 0 < t) (hψ : 0 < ψ)
    (hODE : 2 * (t - 1) * ψ' = 1 / t - ψ)
    (hAtOne : t = 1 → ψ' ≤ -(1 / 4 : ℝ))
    (hhi : 1 < t → 1 / Real.sqrt t ≤ ψ)
    (hlo : t < 1 → ψ ≤ 1 / Real.sqrt t) :
    1 / 2 + t * ψ' / ψ ≤ 1 / (2 * (1 + Real.sqrt t)) := by
  sorry
