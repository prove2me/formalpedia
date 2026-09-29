-- Prove2me | solution 1 for lean_workbook_plus_73506
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:54.265617+00:00
-- url     : https://prove2.me/submissions/86a97a94-da7b-4af6-823a-5674d4e0f3ae

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b + 3 * c) / (4 * a + 5 * b + 6 * c) + (2 * a + 3 * b + c) / (5 * a + 6 * b + 4 * c) + (3 * a + b + 2 * c) / (6 * a + 4 * b + 5 * c) ≤ 6 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
