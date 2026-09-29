-- Prove2me | solution 1 for lean_workbook_plus_65342
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:51.208718+00:00
-- url     : https://prove2.me/submissions/82a99ded-75d7-4f0f-a623-f96aae6c5314

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : ∃ y, y = Real.sqrt (x^2 + Real.sqrt (x^4 + 1)) := by
  norm_num
