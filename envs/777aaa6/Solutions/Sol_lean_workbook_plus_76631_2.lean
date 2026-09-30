-- Prove2me | solution 2 for lean_workbook_plus_76631
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:32.841337+00:00
-- url     : https://prove2.me/submissions/b23730de-9f5f-44f6-9dea-fcd95f291fd5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (9 / (a + b + c)) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
