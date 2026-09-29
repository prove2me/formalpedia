-- Prove2me | solution 1 for lean_workbook_plus_34891
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:32.635704+00:00
-- url     : https://prove2.me/submissions/fb23c7a0-d974-4244-aa6c-e698462c1ea6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (b^2 + c^2) / 4 + (c - a) * (b - a) > 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
