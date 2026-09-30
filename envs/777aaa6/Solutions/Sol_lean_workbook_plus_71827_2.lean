-- Prove2me | solution 2 for lean_workbook_plus_71827
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:40.611334+00:00
-- url     : https://prove2.me/submissions/f097850a-0c82-4109-a56b-1d38550c69a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a + 1) / (a ^ 2 + a + 1) + (b + 1) / (b ^ 2 + b + 1) + (c + 1) / (c ^ 2 + c + 1) ≤ 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
