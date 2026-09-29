-- Prove2me | solution 1 for lean_workbook_plus_70401
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:23.896283+00:00
-- url     : https://prove2.me/submissions/c1674fa4-f248-4c84-ab0a-fab8d8c48adb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (2 * b) + (a + b) / (c + a) + (b + c) / (a + b)) ≥ 5 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
