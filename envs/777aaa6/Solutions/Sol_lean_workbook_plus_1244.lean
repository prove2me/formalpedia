-- Prove2me | solution 1 for lean_workbook_plus_1244
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:22.895427+00:00
-- url     : https://prove2.me/submissions/9eee3030-5f80-453f-9847-75e398a8511d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ (x + y + z) ^ 2 / 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
