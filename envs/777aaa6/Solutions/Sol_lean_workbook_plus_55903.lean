-- Prove2me | solution 1 for lean_workbook_plus_55903
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:04.933385+00:00
-- url     : https://prove2.me/submissions/ac9a0503-88ed-4882-8c0a-848f66e4a4f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) :  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 >= 0 := by
  (intros; positivity)
