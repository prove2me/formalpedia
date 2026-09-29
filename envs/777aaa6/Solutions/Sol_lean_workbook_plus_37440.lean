-- Prove2me | solution 1 for lean_workbook_plus_37440
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:46.164805+00:00
-- url     : https://prove2.me/submissions/b757f45b-c1b8-4a9e-ba6b-358039601d0c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a + b + c = 1) : a^2 + b^2 + c^2 ≥ 1/3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
