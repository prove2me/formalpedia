-- Prove2me | solution 1 for lean_workbook_plus_20616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:46.945079+00:00
-- url     : https://prove2.me/submissions/4e4a0f36-f3b4-44e1-9532-795767525d07

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 5 + (b - c) ^ 5 + (c - a) ^ 5 = 0 → (5 / 2 * (a - c) * (c - b) * (b - a)) * ((a + c - 2 * b) ^ 2 + (a + b - 2 * c) ^ 2 + (b + c - 2 * a) ^ 2) = 0 := by
  (intros; linarith)
