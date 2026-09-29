-- Prove2me | solution 1 for lean_workbook_plus_27928
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:06:06.812027+00:00
-- url     : https://prove2.me/submissions/fc72760c-5b71-4efe-9c4b-c3c6be93156d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 3 * (x + y + z) ^ 2 / 9 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
