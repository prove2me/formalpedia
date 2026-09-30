-- Prove2me | solution 1 for lean_workbook_plus_13602
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:44:18.969958+00:00
-- url     : https://prove2.me/submissions/f57daa0a-5610-4886-9b97-fb33e14dcf01

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 ≥ x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
