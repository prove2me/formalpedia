-- Prove2me | solution 1 for lean_workbook_plus_65220
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:12:34.65822+00:00
-- url     : https://prove2.me/submissions/bbadf9f8-ea71-4586-b017-27f1e4bd6fdf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a : ℝ) : (a^6 + 1) / 2 + (a^6 + 2) / 3 + (a^6 + 5) / 6 ≥ a^3 + a^2 + a := by
  have hfactor : 0 ≤ (a^2+a)^2 + 2*(a+3/4)^2 + (7:ℝ)/8 := by positivity
  have hp := mul_nonneg (sq_nonneg (a-1)) hfactor
  nlinarith
