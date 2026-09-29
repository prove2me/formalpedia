-- Prove2me | solution 1 for lean_workbook_plus_22412
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:31:37.807416+00:00
-- url     : https://prove2.me/submissions/5e43b298-aa05-4612-9f9c-9e23aa406099

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (x : ℝ) : x ^ 4 - x ^ 3 + x ^ 2 - x + 21 / 64 > 0 := by
  nlinarith [sq_nonneg (x^2-x/2-1/16),sq_nonneg (x-17/28)]
