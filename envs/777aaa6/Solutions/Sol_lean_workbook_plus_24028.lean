-- Prove2me | solution 1 for lean_workbook_plus_24028
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:55.11053+00:00
-- url     : https://prove2.me/submissions/3baf3403-9811-4b2a-b467-74cc194d5923

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * (x + y + z) = 3 * y * z) : (x + y) ^ 3 + (x + z) ^ 3 + 3 * (x + y) * (y + z) * (z + x) ≤ 5 * (y + z) ^ 3 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
