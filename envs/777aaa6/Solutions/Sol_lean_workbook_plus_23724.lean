-- Prove2me | solution 1 for lean_workbook_plus_23724
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:46:56.515257+00:00
-- url     : https://prove2.me/submissions/bac36fdc-3579-49d1-b1da-06d2558fde5c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) :  (a - b) ^ 2 * (a - c) ^ 2 * (b - c) ^ 2 ≥ 0 := by
  (intros; positivity)
