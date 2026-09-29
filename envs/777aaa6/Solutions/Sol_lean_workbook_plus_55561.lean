-- Prove2me | solution 1 for lean_workbook_plus_55561
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:03:06.971001+00:00
-- url     : https://prove2.me/submissions/4a09598d-c013-463e-aad7-abe544916f18

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) : (a - b) / (b + c) + (b - c) / (c + a) + (c - a) / (a + b) ≥ 0 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos hab hbc, mul_pos hab hca, mul_pos hbc hca])
