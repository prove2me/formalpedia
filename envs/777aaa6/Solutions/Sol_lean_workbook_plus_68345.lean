-- Prove2me | solution 1 for lean_workbook_plus_68345
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:36.900579+00:00
-- url     : https://prove2.me/submissions/8574bac2-f813-4d37-b9fc-587f7b94132d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (1 / a + 1 / b + 1 / c + 1 / (a + 1) + 1 / (b + 1) + 1 / (c + 1)) = 9 / 2) : a * b * c ≥ 1 := by
  (intros; simp_all)
