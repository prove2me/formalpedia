-- Prove2me | solution 1 for lean_workbook_plus_41540
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:42.234604+00:00
-- url     : https://prove2.me/submissions/136159d7-3c73-49ae-86e4-1be4797154fc

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b / (a + b + 1) + c * d / (c + d + 1)) < ((a + c) * (b + d) / (a + b + c + d + 1)) := by
  have hP : 0 < a + b + 1 := by positivity
  have hQ : 0 < c + d + 1 := by positivity
  have hS : 0 < a + b + c + d + 1 := by positivity
  have key : (a + c) * (b + d) / (a + b + c + d + 1) - (a * b / (a + b + 1) + c * d / (c + d + 1))
      = ((a * d - b * c) ^ 2 + a ^ 2 * d + b ^ 2 * c + a * d ^ 2 + b * c ^ 2 + a * d + b * c)
        / ((a + b + 1) * (c + d + 1) * (a + b + c + d + 1)) := by
    field_simp
    ring
  have hpos : 0 < ((a * d - b * c) ^ 2 + a ^ 2 * d + b ^ 2 * c + a * d ^ 2 + b * c ^ 2 + a * d + b * c)
        / ((a + b + 1) * (c + d + 1) * (a + b + c + d + 1)) := by positivity
  linarith
