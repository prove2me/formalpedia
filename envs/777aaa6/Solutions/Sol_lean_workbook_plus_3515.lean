-- Prove2me | solution 1 for lean_workbook_plus_3515
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:58.298583+00:00
-- url     : https://prove2.me/submissions/01fe6fd0-4741-405a-9339-f75b6386fcff

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x + y - z) ^ 2 + (y + z - x) ^ 2 + (z + x - y) ^ 2 ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
