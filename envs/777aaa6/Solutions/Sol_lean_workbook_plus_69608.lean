-- Prove2me | solution 1 for lean_workbook_plus_69608
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:18.996472+00:00
-- url     : https://prove2.me/submissions/b43772a5-c0b0-4951-a7c5-dd8459158f60

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h₁ : 1.06 * x = 318) : x = 300 := by
  (intros; linarith)
