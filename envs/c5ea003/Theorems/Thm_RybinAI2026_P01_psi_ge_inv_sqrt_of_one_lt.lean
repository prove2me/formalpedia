-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_ge_inv_sqrt_of_one_lt
-- name    : RybinAI2026.P01.psi_ge_inv_sqrt_of_one_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:34:00.106612+00:00
-- url     : https://prove2.me/theorems/5b60e73e-4d13-4664-8dff-e21e5bff790f
-- title:
--   Integral definition of psi above one
-- statement:
--   For t>1, the integral psi(t)=integral from 0 to 1 of 1/(1+(t-1)s²) is at least 1/sqrt(t). This is the t>1 branch needed by the logarithmic-slope envelope.
-- source:
--   Integral-form psi comparison from the diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md; uses the proved arctangent scalar child.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_arctan_lower_slope

theorem RybinAI2026.P01.psi_ge_inv_sqrt_of_one_lt (t : ℝ) (ht : 1 < t) :
    1 / Real.sqrt t ≤ ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ := by
  sorry
