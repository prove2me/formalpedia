-- Prove2me | solution 2 for lean_workbook_plus_70131
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:52.412587+00:00
-- url     : https://prove2.me/submissions/b010a05e-09ac-4fc4-86b7-5e86ac7d915f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (5 * a + c) / (b + c) + 6 * b / (c + a) + (5 * c + a) / (a + b) ≥ 9 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
