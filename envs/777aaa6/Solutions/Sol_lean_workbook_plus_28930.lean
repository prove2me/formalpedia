-- Prove2me | solution 1 for lean_workbook_plus_28930
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:58.22217+00:00
-- url     : https://prove2.me/submissions/9e4974cd-f492-487b-b069-286ee20eb2ab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ a ^ 3 + b ^ 3 + c ^ 3 + 15 * a * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
