-- Prove2me | Theorems.Thm_RybinAI2026_P01_arctan_lower_slope
-- name    : RybinAI2026.P01.arctan_lower_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:07:00.536418+00:00
-- url     : https://prove2.me/theorems/0246a2fa-527d-4456-8a8d-bf4fdc10c720
-- title:
--   Lower slope bound for arctangent
-- statement:
--   For every nonnegative real x, x divided by sqrt(1+x²) is at most arctan(x). In the diagonal pair-contraction proof this is the t>1 scalar branch of the logarithmic-slope envelope, after the substitution x=sqrt(t-1).
-- source:
--   Scalar inequality used in the t>1 case of the slope-envelope proof recorded in artifacts/p01_slack/2026-09-29-no-w-pair.md, for RybinAI2026.P01.matrix_integral_inequality.

import Mathlib

theorem RybinAI2026.P01.arctan_lower_slope (x : ℝ) (hx : 0 ≤ x) :
    x / Real.sqrt (1 + x ^ 2) ≤ Real.arctan x := by
  sorry
