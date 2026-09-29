-- Prove2me | solution 1 for lean_workbook_plus_4026
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:42.274998+00:00
-- url     : https://prove2.me/submissions/c36efa54-3344-46a8-b0db-18ceb568c400

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) :
  2 * (x - y) * (y - z) * (z - t) * (t - x) + (x - z) ^ 2 * (y - t) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t)])
