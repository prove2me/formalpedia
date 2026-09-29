-- Prove2me | solution 1 for lean_workbook_plus_54325
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:44:38.442744+00:00
-- url     : https://prove2.me/submissions/85bd0c13-7478-4fd3-8017-99980a215ca0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : 1 < a) (hbc : 1 < b) (hca : 1 < c)(habc : a * b * c = 1) : 5 * (a + b + c) - 4 * a * b * c ≥ 9 := by
  (intros; linarith)
