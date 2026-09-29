-- Prove2me | solution 1 for lean_workbook_plus_72157
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:23.801569+00:00
-- url     : https://prove2.me/submissions/cb940f24-1262-443a-a705-0d793175883c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) : (a - 0.5) ^ 2 + (b - 1) ^ 2 + (c - 1.5) ^ 2 + (d - 1) ^ 2 + (e - 0.5) ^ 2 ≥ 0 := by
  (intros; positivity)
