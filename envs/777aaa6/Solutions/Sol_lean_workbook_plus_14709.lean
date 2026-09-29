-- Prove2me | solution 1 for lean_workbook_plus_14709
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:05.337011+00:00
-- url     : https://prove2.me/submissions/5b723b8c-36ef-4bec-87f1-fc9c9b017a0a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) = 4) : 1 / a + 1 / b + 1 / c + b / (c * a) ≥ 27 / 8 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
