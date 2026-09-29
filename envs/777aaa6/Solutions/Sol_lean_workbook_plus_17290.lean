-- Prove2me | solution 1 for lean_workbook_plus_17290
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:50.808284+00:00
-- url     : https://prove2.me/submissions/94847ffb-e904-425c-967e-3961cde739d0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a / (a + 2 * b + 1) + b / (b + 2 * a + 1) = 1 / 4 → a + b ≤ 2 / 5) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
