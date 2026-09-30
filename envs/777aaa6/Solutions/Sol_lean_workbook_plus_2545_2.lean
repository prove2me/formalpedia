-- Prove2me | solution 2 for lean_workbook_plus_2545
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:26:00.348393+00:00
-- url     : https://prove2.me/submissions/f2208745-b1cb-4b8c-a5d6-8c0fd25a6ae1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : 0 < a) (hbc : 0 < b) (hca : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c), mul_pos hab hbc, mul_pos hab hca, mul_pos hbc hca])
