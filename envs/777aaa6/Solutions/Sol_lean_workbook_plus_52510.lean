-- Prove2me | solution 1 for lean_workbook_plus_52510
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:25.30985+00:00
-- url     : https://prove2.me/submissions/c0371793-a375-4d61-97b7-57127b267dee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 / (a + b) ^ 2 / (b + c) ^ 2 / (c + a) ^ 2 ≥ 0 := by
  (intros; positivity)
