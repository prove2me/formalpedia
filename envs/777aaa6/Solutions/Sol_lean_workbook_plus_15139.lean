-- Prove2me | solution 1 for lean_workbook_plus_15139
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:19.127971+00:00
-- url     : https://prove2.me/submissions/daaee91e-1987-4c25-b68a-3fe03b6498a4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : |2 * x| ≤ 1 + x ^ 2 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1)]
