-- Prove2me | solution 1 for lean_workbook_plus_71559
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:46.815925+00:00
-- url     : https://prove2.me/submissions/9d7e3159-1a78-4240-928a-abe9021dafe5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + 1) ^ 3 + (y + z + 1) ^ 3 + (z + x + 1) ^ 3 > (4 / 3) * (x + y + z + 1) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
