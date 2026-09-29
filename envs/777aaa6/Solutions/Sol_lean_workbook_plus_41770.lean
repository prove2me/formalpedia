-- Prove2me | solution 1 for lean_workbook_plus_41770
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:30:02.10878+00:00
-- url     : https://prove2.me/submissions/b1118f2d-55ee-4f99-9da5-ef962c5878ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x ^ 3 + y ^ 3 + z ^ 3 + x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≥ 2 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
