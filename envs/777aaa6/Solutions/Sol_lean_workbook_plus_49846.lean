-- Prove2me | solution 1 for lean_workbook_plus_49846
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:24.748961+00:00
-- url     : https://prove2.me/submissions/7a80cf07-c795-4294-8b6c-fa3b9863ff54

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 ≥ y * (2 * x + y + 2 * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
