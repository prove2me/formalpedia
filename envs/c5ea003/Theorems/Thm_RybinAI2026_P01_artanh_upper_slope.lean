-- Prove2me | Theorems.Thm_RybinAI2026_P01_artanh_upper_slope
-- name    : RybinAI2026.P01.artanh_upper_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T22:07:16.043281+00:00
-- url     : https://prove2.me/theorems/8604d309-9145-47cb-9f3e-d78d9f8cfbd5
-- title:
--   Upper slope bound for inverse hyperbolic tangent
-- statement:
--   For 0≤x<1, inverse hyperbolic tangent artanh(x) is at most x divided by sqrt(1-x²). In the diagonal pair-contraction proof this is the 0<t<1 scalar branch of the logarithmic-slope envelope, after x=sqrt(1-t).
-- source:
--   Scalar inequality used in the 0<t<1 case of the slope-envelope proof recorded in artifacts/p01_slack/2026-09-29-no-w-pair.md, for RybinAI2026.P01.matrix_integral_inequality.

import Mathlib

theorem RybinAI2026.P01.artanh_upper_slope (x : ℝ)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    Real.artanh x ≤ x / Real.sqrt (1 - x ^ 2) := by
  sorry
