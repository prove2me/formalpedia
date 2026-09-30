-- Prove2me | solution 1 for lean_workbook_plus_63395
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:31:04.50168+00:00
-- url     : https://prove2.me/submissions/f4b359b9-d299-4e09-81dd-1c400f514820

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (h : x * y * z < 0) :
    x ^ 2 + y ^ 2 + z ^ 2 ≥ Real.sqrt (x * y * z * (x + y + z)) := by
  apply (Real.sqrt_le_left (by positivity)).mpr
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
    sq_nonneg (z * x - x * y), sq_nonneg (x ^ 2), sq_nonneg (y ^ 2),
    sq_nonneg (z ^ 2), sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)]

#print axioms solution
