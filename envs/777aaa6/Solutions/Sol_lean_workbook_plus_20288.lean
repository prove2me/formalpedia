-- Prove2me | solution 1 for lean_workbook_plus_20288
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:16:48.831811+00:00
-- url     : https://prove2.me/submissions/49d06741-8d46-44eb-85cf-84553d5a65b7

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : (b - c) ^ 2 + (c - a) ^ 2 ≥ 1 / 2 * (a - b) ^ 2 := by
  nlinarith [sq_nonneg (a + b - 2 * c)]
