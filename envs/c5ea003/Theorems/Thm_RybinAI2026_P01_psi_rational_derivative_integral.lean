-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_rational_derivative_integral
-- name    : RybinAI2026.P01.psi_rational_derivative_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T23:52:12.109113+00:00
-- url     : https://prove2.me/theorems/8a25f2be-d70d-4c3c-ac79-6459c42f242e
-- title:
--   Evaluate the rational derivative integral
-- statement:
--   For positive t, the integral from zero to one of the derivative of s/(1+(t-1)s^2) equals 1/t. This is the fundamental-theorem-of-calculus component in the integration-by-parts identity for the scalar function psi.
-- source:
--   Fundamental-theorem-of-calculus step in the aligned diagonal proof in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.psi_rational_derivative_integral (t : ℝ) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..1, (1 - (t - 1) * s ^ 2) / (1 + (t - 1) * s ^ 2) ^ 2 = 1 / t := by
  sorry
