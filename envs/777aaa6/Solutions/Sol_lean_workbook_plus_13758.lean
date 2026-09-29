-- Prove2me | solution 1 for lean_workbook_plus_13758
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:13.57771+00:00
-- url     : https://prove2.me/submissions/596be25d-6bab-4b7d-b367-f08c8c22c039

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 3 * x * y * z * (x + y + z) ≥ 2 * (x * y + y * z + x * z) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
