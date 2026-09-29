-- Prove2me | solution 1 for lean_workbook_plus_17436
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:27.650412+00:00
-- url     : https://prove2.me/submissions/bc9807fb-a27d-4351-a371-0803f5bfc5dc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 1) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 12) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 123) : 16 * a + 25 * b + 36 * c + 49 * d = 334 := by
  (intros; linarith)
