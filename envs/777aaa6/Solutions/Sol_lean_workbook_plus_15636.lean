-- Prove2me | solution 1 for lean_workbook_plus_15636
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:59.710343+00:00
-- url     : https://prove2.me/submissions/76a01ad5-a251-42c1-aed1-117ccc7df462

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
