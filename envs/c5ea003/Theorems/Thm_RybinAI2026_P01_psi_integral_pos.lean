-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_integral_pos
-- name    : RybinAI2026.P01.psi_integral_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:55:00.82904+00:00
-- url     : https://prove2.me/theorems/0558b978-e7a5-4cc9-bb80-a02bba5a9f4b
-- title:
--   Positivity of the defining psi integral
-- statement:
--   For every t>0, the defining integral psi(t)=integral from 0 to 1 of 1/(1+(t-1)s²) is strictly positive. This supplies the positivity hypothesis for the logarithmic-slope expression.
-- source:
--   Positive-integrand fact for the integral psi in the diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.psi_integral_pos (t : ℝ) (ht : 0 < t) :
    0 < ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  sorry
