-- Prove2me | solution 1 for lean_workbook_plus_23606
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:18.531854+00:00
-- url     : https://prove2.me/submissions/7b910758-b25e-4b91-a0ba-df0dd6abeae3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b x: ℝ) : (a - b) ^ 2 * (x ^ 2 - a * b) ^ 2 ≥ 0 := by
  (intros; positivity)
