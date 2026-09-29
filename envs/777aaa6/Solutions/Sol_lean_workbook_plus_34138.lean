-- Prove2me | solution 1 for lean_workbook_plus_34138
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:16.922133+00:00
-- url     : https://prove2.me/submissions/e4bd76e1-7dd4-4f96-abe2-6c4435fd2026

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : 5 * x = 3 * 4 → x = 12 / 5 := by
  (intros; linarith)
