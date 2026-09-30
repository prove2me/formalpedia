-- Prove2me | solution 1 for lean_workbook_plus_21142
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:57.427282+00:00
-- url     : https://prove2.me/submissions/a552627a-dfb9-49ac-889f-a34760deae6e

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (1 + a) - 1 / (1 + b) + a / (a + b) < 1 := by
  have key : 1 / (1 + a) - 1 / (1 + b) + a / (a + b)
      = 1 - (a * b ^ 2 + b + a ^ 2 + a * b) / ((1 + a) * (1 + b) * (a + b)) := by
    field_simp
    ring
  rw [key]
  have : 0 < (a * b ^ 2 + b + a ^ 2 + a * b) / ((1 + a) * (1 + b) * (a + b)) := by positivity
  linarith
