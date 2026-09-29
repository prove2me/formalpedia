-- Prove2me | solution 1 for lean_workbook_plus_54371
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:35.268202+00:00
-- url     : https://prove2.me/submissions/27695c24-57dc-4c9a-8780-12fe6f4ba2be

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 3 * (a + b + c) ^ 4 ≥ 6 * (a ^ 2 + b ^ 2 + c ^ 2) * (a + b + c) ^ 2 := by
  nlinarith [sq_nonneg ((a^2+b^2+c^2)-(a+b+c)^2)]
