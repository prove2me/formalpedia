-- Prove2me | solution 1 for lean_workbook_plus_49196
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:54.088942+00:00
-- url     : https://prove2.me/submissions/688b48b2-671f-4c9a-8a08-caa9b2db595c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) (h1: a >= 2) (h2: a * b * c = 1) : (1 / 2) * a ^ 2 + b ^ 2 + c ^ 2 - b * c >= 5 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
