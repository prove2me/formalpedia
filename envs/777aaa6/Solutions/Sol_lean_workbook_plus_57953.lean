-- Prove2me | solution 1 for lean_workbook_plus_57953
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:45:37.036867+00:00
-- url     : https://prove2.me/submissions/07c830f5-9b48-4ad1-85b1-0be968b6be87

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 ≥ 3 * (x * y + y * z + z * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
