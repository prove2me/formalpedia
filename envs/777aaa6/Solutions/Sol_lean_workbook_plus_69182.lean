-- Prove2me | solution 1 for lean_workbook_plus_69182
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:35.955917+00:00
-- url     : https://prove2.me/submissions/250c70e7-aa60-4b1a-aef7-942e1254ca93

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : x^2 + y^2 - 2 * x * y + 4 * x - 4 * y = 5 ↔ (x - y)^2 + 4 * (x - y) - 5 = 0 := by
  constructor <;> intro h <;> linear_combination h
