-- Prove2me | solution 1 for lean_workbook_plus_54143
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:15.466714+00:00
-- url     : https://prove2.me/submissions/725bec67-a12d-4dc1-9e60-7483c7b1effb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (5 * c + 4 * a) + (3 * c) / (4 * a + 4 * b + c) + (c + 2 * a) / (a + 2 * b + 6 * c) ≥ 1 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
