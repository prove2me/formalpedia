-- Prove2me | solution 1 for lean_workbook_plus_31418
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:38.85997+00:00
-- url     : https://prove2.me/submissions/b91f69e7-4e68-4b38-8523-fe17ef9f6b36

import Mathlib.Analysis.Complex.Basic

theorem solution (s : ℝ) : 3 = s * Real.sqrt 3 / 2 → s = 2 * Real.sqrt 3 := by
  intro h
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [h, h3, hpos]
