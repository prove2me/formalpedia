-- Prove2me | solution 1 for lean_workbook_plus_55251
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:39.471988+00:00
-- url     : https://prove2.me/submissions/c89f2dcd-6e1d-4022-a508-589e00b7ea8a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x * y + y * z + z * x = -9) : 2 * x ^ 2 + 10 * y ^ 2 + 16 * z ^ 2 - 16 * y * z ≥ -18 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
