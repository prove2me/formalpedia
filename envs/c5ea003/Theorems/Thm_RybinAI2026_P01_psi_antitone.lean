-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_antitone
-- name    : RybinAI2026.P01.psi_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T00:11:13.408354+00:00
-- url     : https://prove2.me/theorems/9bc57145-946e-45e9-986e-4b3e5dd1d73f
-- title:
--   The defining psi integral is antitone
-- statement:
--   The scalar function psi(t)=integral from zero to one of (1+(t-1)x^2)^(-1) is antitone for positive t. The denominator increases pointwise with t and remains strictly positive on the interval.
-- source:
--   Monotonicity fact used to establish positivity of eta in the aligned diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md.

import Mathlib

theorem RybinAI2026.P01.psi_antitone (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    (∫ x in (0 : ℝ)..1, (1 + (t - 1) * x ^ 2)⁻¹) ≤
      ∫ x in (0 : ℝ)..1, (1 + (s - 1) * x ^ 2)⁻¹ := by
  sorry
