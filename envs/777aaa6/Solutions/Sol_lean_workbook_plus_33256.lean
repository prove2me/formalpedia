-- Prove2me | solution 1 for lean_workbook_plus_33256
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:30.135208+00:00
-- url     : https://prove2.me/submissions/f48d61ee-a3fc-4269-b5d6-2fc40a1c34f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : 4 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ 4 * (x * y + y * z + x * z) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
