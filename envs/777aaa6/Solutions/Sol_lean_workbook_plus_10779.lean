-- Prove2me | solution 1 for lean_workbook_plus_10779
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:27.149575+00:00
-- url     : https://prove2.me/submissions/97c05247-2196-4cd7-9689-b154ff8ae5f5

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ) :
  64 * (x^2 + 4 * x + 4) * (1 - x) = (x^2 - 22 * x + 121) * (x + 1) ↔ 65 * x^3 + 171 * x^2 + 99 * x - 135 = 0 := by
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h
