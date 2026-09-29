-- Prove2me | solution 1 for lean_workbook_plus_64328
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:10.016466+00:00
-- url     : https://prove2.me/submissions/42aaeb9c-5a35-4810-bf9a-436deb9b1b52

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a / (b + 1) + b / (a + 1) + 1 / (a + b + 1) = 4 / 3 → a + b ≤ 2) := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
