-- Prove2me | solution 2 for lean_workbook_plus_65330
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:45.795283+00:00
-- url     : https://prove2.me/submissions/96c73dd4-dc35-47c8-8613-a3450eb4c157

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :  (a - b) * (b - c) * (c - d) * (d - a) + (a - c) ^ 2 * (b - d) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
