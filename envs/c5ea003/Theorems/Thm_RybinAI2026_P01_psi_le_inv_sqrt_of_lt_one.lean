-- Prove2me | Theorems.Thm_RybinAI2026_P01_psi_le_inv_sqrt_of_lt_one
-- name    : RybinAI2026.P01.psi_le_inv_sqrt_of_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:44:11.958294+00:00
-- url     : https://prove2.me/theorems/7a4e09b4-143b-45c2-b74a-cdb42f6d24f8
-- title:
--   Integral definition of psi below one
-- statement:
--   For 0<t<1, the integral psi(t)=integral from 0 to 1 of 1/(1+(t-1)s²) is at most 1/sqrt(t). This is the lower-parameter branch needed by the logarithmic-slope envelope.
-- source:
--   Integral-form psi comparison from the diagonal pair-contraction proof in artifacts/p01_slack/2026-09-29-no-w-pair.md; uses the proved artanh scalar child.

import Mathlib
import Theorems.Thm_RybinAI2026_P01_artanh_upper_slope

theorem RybinAI2026.P01.psi_le_inv_sqrt_of_lt_one (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹ ≤ 1 / Real.sqrt t := by
  sorry
