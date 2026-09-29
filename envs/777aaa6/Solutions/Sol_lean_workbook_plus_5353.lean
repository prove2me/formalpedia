-- Prove2me | solution 1 for lean_workbook_plus_5353
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:56.144529+00:00
-- url     : https://prove2.me/submissions/45cf0b62-be3c-465a-bdf4-b8710554b051

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1 / a + 1 / b = 1) : 4 * a * b + 3 / (a + b) ≤ 35 / 4 + a ^ 2 + b ^ 2 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
