-- Prove2me | solution 1 for lean_workbook_plus_55103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:24.656824+00:00
-- url     : https://prove2.me/submissions/ea4befca-62f6-439e-b72c-607f5c65cdb9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a < 0) (hb : b < 0) (hc : c < 0) (habc : a + b + c = 3) : 2 * (a ^ 2 + b ^ 2 + c ^ 2 + 9) * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a + 3 * a * b * c) ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b * c) ^ 2 := by
  (intros; linarith)
