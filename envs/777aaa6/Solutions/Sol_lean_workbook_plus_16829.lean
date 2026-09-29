-- Prove2me | solution 1 for lean_workbook_plus_16829
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:09.835198+00:00
-- url     : https://prove2.me/submissions/05753a76-592a-477b-9dc6-aec194da6f9d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a ≥ 3 + (c - a) ^ 2 / (a * (b + c)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
