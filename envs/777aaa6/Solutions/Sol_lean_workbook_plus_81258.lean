-- Prove2me | solution 1 for lean_workbook_plus_81258
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:58:23.810624+00:00
-- url     : https://prove2.me/submissions/dc9791d6-cc24-4bf6-b43e-6cd2d189d6e4

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) :
    x^2 * (3 * y + x)^2 + y^2 * (3 * z + y)^2 -
      2 * (x + y)^2 * y * (3 * z + x) ≥ 0 := by
  nlinarith [sq_nonneg (3*y*z - x*(x + 2*y)), sq_nonneg (y*(x - y))]
