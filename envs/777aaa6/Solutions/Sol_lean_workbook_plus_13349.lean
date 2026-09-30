-- Prove2me | solution 1 for lean_workbook_plus_13349
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:42.21295+00:00
-- url     : https://prove2.me/submissions/16b8a3be-42b0-4e59-a081-42011f4944f8

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z: ℝ) : x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 ≥ x * y * z * (x + y + z) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
