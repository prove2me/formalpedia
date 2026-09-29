-- Prove2me | solution 1 for lean_workbook_plus_1120
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:17:15.174344+00:00
-- url     : https://prove2.me/submissions/a3d3f993-5a13-40fe-913f-57a916af0a85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 ≤ k) : (a + k) / (b + c + 2 * k) + (b + k) / (c + a + 2 * k) + (c + k) / (a + b + 2 * k) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (k), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - k), sq_nonneg (b - c), sq_nonneg (b - k), sq_nonneg (c - k), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + k), sq_nonneg (b + c), sq_nonneg (b + k), sq_nonneg (c + k), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
