-- Prove2me | solution 1 for lean_workbook_plus_17820
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:50.285124+00:00
-- url     : https://prove2.me/submissions/d0e18011-fd6b-4de3-884c-410fb42c956d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b ≠ 1) (hab2 : a^2 / (1 + b) + b^2 / (1 + a) = 8 / 3) : 1 / a + 1 / b ≥ 1 := by
  intros
  field_simp at * <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
