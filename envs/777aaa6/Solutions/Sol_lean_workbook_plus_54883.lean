-- Prove2me | solution 1 for lean_workbook_plus_54883
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:55.604709+00:00
-- url     : https://prove2.me/submissions/72ad5dcf-3c57-40c6-8694-87c2faa17953

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (3 * a + b + c) + b / (3 * b + a + c) + c / (3 * c + a + b) : ℝ) ≤ 3 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
