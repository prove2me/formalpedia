-- Prove2me | solution 1 for lean_workbook_plus_59030
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:02.664118+00:00
-- url     : https://prove2.me/submissions/fdefa516-09e6-41d6-9f5f-5fdf814074cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :  (a + b) * (b + c) * (c + a) ≥ 8 * (a + b - c) * (b + c - a) * (c + a - b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
