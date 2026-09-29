-- Prove2me | solution 1 for lean_workbook_plus_18197
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:19.747819+00:00
-- url     : https://prove2.me/submissions/71bf1ee7-0ce2-40dd-8e5a-77c43021efda

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a - b ≥ 0) (hbc : b - c ≥ 0) (hca : c - a ≥ 0) : (13 * a - 5 * b + c) * (a - b) ^ 2 + (13 * b - 5 * c + a) * (b - c) ^ 2 + (13 * c - 5 * a + b) * (c - a) ^ 2 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
