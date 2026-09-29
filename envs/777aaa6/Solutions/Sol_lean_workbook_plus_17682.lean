-- Prove2me | solution 1 for lean_workbook_plus_17682
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:30.777239+00:00
-- url     : https://prove2.me/submissions/26a963af-d580-41b7-8968-b83292cb6c04

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : (1 / (a - 1) / (b - 1) / (c - 1) - 4 / (a + 1) / (b + 1) / (c + 1) = 1 / 16) → 1 / a + 1 / b + 1 / c ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
