-- Prove2me | solution 1 for lean_workbook_plus_34228
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:10.920813+00:00
-- url     : https://prove2.me/submissions/a3596ab8-7a39-4b16-8bb1-6c552cbb48bb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 4 / (a + b) + 1 / b = 1) : a * (2 * b - 3) ≤ 9 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
