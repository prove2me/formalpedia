-- Prove2me | solution 1 for lean_workbook_plus_53107
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:54.589896+00:00
-- url     : https://prove2.me/submissions/0fcc1aec-82ee-4125-84cd-a56d3ebaded7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (a + 3 * b + 3 * c) + (c + a) / (b + 3 * c + 3 * a) + (a + b) / (c + 3 * a + 3 * b) ≤ 6 / 7 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
