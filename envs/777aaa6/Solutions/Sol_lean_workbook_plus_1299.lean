-- Prove2me | solution 1 for lean_workbook_plus_1299
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:15.130378+00:00
-- url     : https://prove2.me/submissions/1daeff12-bf19-4498-9be1-250525b14889

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (1 / (x * (x + 3 * y)) + 1 / (y * (y + 3 * x)) = 1 → x * y ≤ 1 / 2) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
