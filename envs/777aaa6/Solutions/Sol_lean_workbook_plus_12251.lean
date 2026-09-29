-- Prove2me | solution 1 for lean_workbook_plus_12251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:25.45381+00:00
-- url     : https://prove2.me/submissions/0897bdc0-951f-4189-9c57-51fee7b70125

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : Real.sqrt (x ^ 2 + x * y + y ^ 2) ≥ Real.sqrt (3 * x * y) := by
  intros
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
