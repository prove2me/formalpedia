-- Prove2me | solution 1 for lean_workbook_plus_63646
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:03.314185+00:00
-- url     : https://prove2.me/submissions/54fa8831-8c57-4221-93a1-b4cd1d1f0ab4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (2 * a ^ 3 - 9 * a * b ^ 2) ^ 2 + 3 * (6 * a ^ 2 * b - 3 * b ^ 3) ^ 2 = (2 * a ^ 2 + 3 * b ^ 2) ^ 3 := by
  (intros; linarith)
