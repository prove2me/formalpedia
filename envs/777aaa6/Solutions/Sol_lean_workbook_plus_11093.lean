-- Prove2me | solution 1 for lean_workbook_plus_11093
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:08:48.377085+00:00
-- url     : https://prove2.me/submissions/3999b27d-ba63-4766-81ab-6384f5048a65

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) :
  Real.sqrt (x^2 + x * y + y^2) ≥ Real.sqrt (3 * x * y) := by
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (x - y)]
