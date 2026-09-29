-- Prove2me | solution 1 for lean_workbook_plus_46338
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:14.329024+00:00
-- url     : https://prove2.me/submissions/11aeb650-c45e-42bb-a199-33ee64b94d21

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a ^ 4 + b ^ 4) + 17 > 16 * a * b := by
  nlinarith only [sq_nonneg (a^2-b^2),sq_nonneg (a*b-2)]
