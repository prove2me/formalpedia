-- Prove2me | solution 1 for lean_workbook_plus_81099
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:46.068413+00:00
-- url     : https://prove2.me/submissions/3cf67679-f1d4-471e-ac0f-1397f6df59e4

import Mathlib.Tactic

theorem solution (x t : ℝ) (hx : x > t) (ht : t > 0) : 1 > 1 / (t + 1) := by
  rw [gt_iff_lt, div_lt_one (by linarith)]
  linarith
