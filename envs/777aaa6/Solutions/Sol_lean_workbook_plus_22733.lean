-- Prove2me | solution 1 for lean_workbook_plus_22733
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:23.080932+00:00
-- url     : https://prove2.me/submissions/7bb89ba3-ae15-458a-8df6-e04523d71162

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : -3 / 2 < a + b ∧ a + b < -1 / 2 ∧ -9 / 2 < 2 * a + b ∧ 2 * a + b < -7 / 2 ∧ -19 / 2 < 3 * a + b ∧ 3 * a + b < -17 / 2 → False := by
  (intros; linarith)
