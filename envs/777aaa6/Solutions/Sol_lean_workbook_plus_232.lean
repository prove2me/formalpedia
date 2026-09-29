-- Prove2me | solution 1 for lean_workbook_plus_232
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:38.70902+00:00
-- url     : https://prove2.me/submissions/e00e312a-0ff0-42cc-9c03-56293166c87d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b + 1 / (a * b) = 6) : (a + 1) * (b + 1) ≥ 2 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
