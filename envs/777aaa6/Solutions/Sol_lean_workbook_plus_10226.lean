-- Prove2me | solution 1 for lean_workbook_plus_10226
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:38.248687+00:00
-- url     : https://prove2.me/submissions/bc8f2aba-5921-4ab1-9d56-e5c093b10609

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - 1) ^ 2 * (a - 1 / 2) ^ 2 + (b - 1) ^ 2 * (b - 1 / 2) ^ 2 + (c - 1) ^ 2 * (c - 1 / 2) ^ 2 ≥ 0 := by
  (intros; positivity)
