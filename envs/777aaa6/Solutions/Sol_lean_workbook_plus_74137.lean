-- Prove2me | solution 1 for lean_workbook_plus_74137
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:33.142173+00:00
-- url     : https://prove2.me/submissions/3c216f19-3da6-4b49-bb77-c0de15def472

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x + y + z + 4*x*y*z = 1) : x*y + y*z + z*x ≤ 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
