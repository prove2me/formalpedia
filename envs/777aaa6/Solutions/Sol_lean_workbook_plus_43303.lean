-- Prove2me | solution 1 for lean_workbook_plus_43303
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:31.120913+00:00
-- url     : https://prove2.me/submissions/a732cf74-5bc4-4638-b797-639647387f80

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a / (a + 2 * b + 1) + b / (b + 2 * a + 1) = 1 / 2 → a + b ≤ 2) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
