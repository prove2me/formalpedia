-- Prove2me | solution 1 for lean_workbook_plus_72668
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:57.642732+00:00
-- url     : https://prove2.me/submissions/33bce37a-d496-402d-8094-eb72e477fbe5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : (2 * a + b) * (2 * b + a) = 9) : a * b ≤ 1 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
