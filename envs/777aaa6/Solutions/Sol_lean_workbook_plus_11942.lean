-- Prove2me | solution 1 for lean_workbook_plus_11942
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:58.122888+00:00
-- url     : https://prove2.me/submissions/4d9280d2-75ba-4eae-9f15-bc670f838860

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : (2 * a ^ 4 + 2 * b ^ 4 + 2 * (a + b) ^ 4) = (2 * a ^ 2 + 2 * a * b + 2 * b ^ 2) ^ 2 := by
  (intros; linarith)
