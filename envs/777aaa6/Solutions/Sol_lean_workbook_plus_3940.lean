-- Prove2me | solution 1 for lean_workbook_plus_3940
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:24.347152+00:00
-- url     : https://prove2.me/submissions/545c03cc-d279-4540-8754-b842a592ca52

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (h : x + y + z = x*y*z) :
  x * (1 - y ^ 2) * (1 - z ^ 2) + y * (1 - z ^ 2) * (1 - x ^ 2) + z * (1 - x ^ 2) * (1 - y ^ 2) = 4*x*y*z := by
  linear_combination (1 - (x * y + y * z + z * x)) * h
