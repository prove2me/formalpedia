-- Prove2me | solution 1 for lean_workbook_plus_61978
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:23.19828+00:00
-- url     : https://prove2.me/submissions/a1b19b3f-471a-4d68-8371-f366942a7f67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + 1 + 1 ≥ a * b + a * c + b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
