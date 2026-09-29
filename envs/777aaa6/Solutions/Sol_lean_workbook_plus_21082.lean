-- Prove2me | solution 1 for lean_workbook_plus_21082
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:47.213524+00:00
-- url     : https://prove2.me/submissions/62035a01-d600-4c5b-b486-ca1cdfa41bc1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a + b + c = 1) :
  a^2 + b^2 + c^2 ≥ 1 / 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
