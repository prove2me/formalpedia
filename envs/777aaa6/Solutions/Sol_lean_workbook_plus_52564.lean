-- Prove2me | solution 1 for lean_workbook_plus_52564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:45.062339+00:00
-- url     : https://prove2.me/submissions/f0457ef7-8c47-4d8e-b0a1-c95c956f2baf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (y : ℝ) : 243*y^4 + 108*y^3 - 108*y^2 + 32 ≥ 0 := by
  have hq : 0 ≤ 27*y^2-24*y+8 := by nlinarith [sq_nonneg (9*y-4)]
  have hp := mul_nonneg (sq_nonneg (3*y+2)) hq
  nlinarith only [hp]
