-- Prove2me | solution 1 for lean_workbook_plus_51959
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:24.194959+00:00
-- url     : https://prove2.me/submissions/a0e845d8-c854-446d-9ea0-865a2e55e8cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * y * (x + y) + y * z * (y + z) + z * x * (z + x) ≥ 6 * x * y * z := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
