-- Prove2me | solution 1 for lean_workbook_plus_56569
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:42:02.26972+00:00
-- url     : https://prove2.me/submissions/f703e20a-bd2e-4e8d-8ae0-ce00b5af6c98

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 81 * a * b * c * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 27 * (a * b + b * c + c * a) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
