-- Prove2me | solution 1 for lean_workbook_plus_34879
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:27.518637+00:00
-- url     : https://prove2.me/submissions/d1604da6-4dca-4801-9bbb-8cd9aac70a03

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x > 0) (h : 3/8 * x - 5/32 * x = 140) : x = 640 := by
  (intros; linarith)
