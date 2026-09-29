-- Prove2me | solution 1 for lean_workbook_plus_48506
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:48.193835+00:00
-- url     : https://prove2.me/submissions/045e546a-fdb9-4db7-a405-a8b9fedcbb4c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a + b - 2 * c) ^ 4 + (a + c - 2 * b) ^ 4 + (b + c - 2 * a) ^ 4 ≥ 9 * ((a - b) ^ 4 + (a - c) ^ 4 + (b - c) ^ 4) := by
  (intros; linarith)
