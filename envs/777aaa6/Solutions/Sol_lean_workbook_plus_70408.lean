-- Prove2me | solution 1 for lean_workbook_plus_70408
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:21.23647+00:00
-- url     : https://prove2.me/submissions/54196191-ebb9-4f83-8af8-a6d5bbde3495

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b + c) + 2 / 3) * (b / (a + b + c) + 2 / 3) * (c / (a + b + c) + 2 / 3) ≤ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
