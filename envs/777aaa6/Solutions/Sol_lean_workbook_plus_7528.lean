-- Prove2me | solution 1 for lean_workbook_plus_7528
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:01.390174+00:00
-- url     : https://prove2.me/submissions/ecd355e6-1b6c-4553-bcbd-fd96c7c8a4fe

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x * y + z * x ≤ x ^ 2 + (y ^ 2 + z ^ 2) / 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
