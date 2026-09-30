-- Prove2me | solution 2 for lean_workbook_plus_45833
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:31.429445+00:00
-- url     : https://prove2.me/submissions/b1fe55ba-6acf-402d-a18c-45648d9536c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
