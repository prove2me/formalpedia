-- Prove2me | Theorems.Thm_RybinAI2026_P01_eta_envelope_of_sqrt_comparison
-- name    : RybinAI2026.P01.eta_envelope_of_sqrt_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:22:27.158857+00:00
-- url     : https://prove2.me/theorems/655e3186-291a-43a9-9b28-dff8c37a92ec
-- title:
--   Slope envelope from square-root comparisons
-- statement:
--   Let t and ψ be positive. If ψ is at least 1/sqrt(t) above one and at most 1/sqrt(t) below one, then the logarithmic-slope expression (1-ψ)/(2(t-1)ψ), with value 1/6 at t=1, is bounded above by 1/(2(1+sqrt(t))). This is the algebraic bridge used in the diagonal pair-contraction slope-envelope proof.
-- source:
--   Algebraic η-envelope step from the diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md, for RybinAI2026.P01.matrix_integral_inequality.

import Mathlib

theorem RybinAI2026.P01.eta_envelope_of_sqrt_comparison (t ψ : ℝ) (ht : 0 < t) (hψ : 0 < ψ) (hhi : 1 < t → 1 / Real.sqrt t ≤ ψ) (hlo : t < 1 → ψ ≤ 1 / Real.sqrt t) :
    (if t = 1 then (1 : ℝ) / 6 else (1 - ψ) / (2 * (t - 1) * ψ)) ≤ 1 / (2 * (1 + Real.sqrt t)) := by
  sorry
