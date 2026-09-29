-- Prove2me | solution 1 for lean_workbook_plus_72102
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:14.672256+00:00
-- url     : https://prove2.me/submissions/80c007c0-5cfd-42a4-8c88-42794eb45cce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (a + 2 * (b + c)) + b / (b + 2 * (c + a)) + c / (c + 2 * (a + b)) ≥ 3 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
