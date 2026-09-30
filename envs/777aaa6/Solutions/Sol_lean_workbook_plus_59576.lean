-- Prove2me | solution 1 for lean_workbook_plus_59576
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:59:23.212702+00:00
-- url     : https://prove2.me/submissions/a102fbc1-4ad7-427e-8202-4ebefce9d9ad

import Mathlib.Analysis.Complex.Basic

theorem solution :  ∀ x y z u v w : ℝ, (x - u) ^ 2 + (y - v) ^ 2 + (z - w) ^ 2 ≥ 1 / 2 * ((x - z) * (x - u - v + z) + (y - x) * (y - v - w + x) + (z - y) * (z - w - u + y)) := by
  intro x y z u v w
  nlinarith [sq_nonneg (x - u), sq_nonneg (y - v), sq_nonneg (z - w),
    sq_nonneg (x - w), sq_nonneg (y - u), sq_nonneg (z - v)]
