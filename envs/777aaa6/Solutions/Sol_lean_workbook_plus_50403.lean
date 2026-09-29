-- Prove2me | solution 1 for lean_workbook_plus_50403
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:20:41.835004+00:00
-- url     : https://prove2.me/submissions/c784e9ff-7a62-43f6-afc8-d8bbb997d348

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (a + b) + 2 / (b + c) + 2 / (c + a) ≥ 9 / (a + b + c) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
