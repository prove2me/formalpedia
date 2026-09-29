-- Prove2me | solution 1 for lean_workbook_plus_20219
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:21.831531+00:00
-- url     : https://prove2.me/submissions/5317f43b-0e51-477e-9b02-f46660ce9df6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x * y) ^ 2 + (y * z) ^ 2 + (z * x) ^ 2 ≥ (x + y + z) * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
