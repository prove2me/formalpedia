-- Prove2me | solution 1 for lean_workbook_plus_54432
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:00:56.263433+00:00
-- url     : https://prove2.me/submissions/33a1fea2-a8c1-4852-8f0f-91d121ff3317

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 3 - 27 * x * y * z ≤ 11 * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
