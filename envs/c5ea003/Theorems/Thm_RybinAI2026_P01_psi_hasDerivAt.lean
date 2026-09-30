-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_hasDerivAt
-- name    : RybinAI2026.P01.psi_hasDerivAt
-- status  : Open
-- author  : @WillR
-- created : 2026-09-29T23:45:28.507988+00:00
-- url     : https://prove2.me/theorems/46ce7bcb-a686-4590-b2b0-2cc4d76483d1
-- title:
--   Differentiate the defining psi integral
-- statement:
--   For every positive t, the scalar integral psi(t)=integral from 0 to 1 of (1+(t-1)s^2)^(-1) is differentiable, with derivative equal to the integral of the pointwise derivative -s^2(1+(t-1)s^2)^(-2). This is the calculus bridge needed for the diagonal pair-contraction slope argument.
-- source:
--   Differentiation under the integral sign for psi in the aligned diagonal proof in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.psi_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..1, (1 + (x - 1) * s ^ 2)⁻¹)
      (∫ s in (0 : ℝ)..1, -(s ^ 2 * (1 + (t - 1) * s ^ 2)⁻¹ ^ 2)) t := by
  sorry
