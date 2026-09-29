-- Prove2me | solution 1 for lean_workbook_plus_15566
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:25.626949+00:00
-- url     : https://prove2.me/submissions/736118f1-fe7c-45b1-a8da-7bef6c118606

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b + c) ^ 2 * (a + c - b) ^ 2 + (b - c + a) ^ 2 * (b + a - c) ^ 2 + (c - a + b) ^ 2 * (c + b - a) ^ 2 ≥ 0 := by
  (intros; positivity)
