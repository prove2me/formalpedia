-- Prove2me | solution 1 for lean_workbook_plus_57589
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:46:03.731088+00:00
-- url     : https://prove2.me/submissions/0ca95e55-5cb5-4389-98a3-1ea319416d87

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≥ 0 := by
  (intros; positivity)
