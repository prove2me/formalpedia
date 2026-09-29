-- Prove2me | solution 1 for lean_workbook_plus_18133
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:56:16.995909+00:00
-- url     : https://prove2.me/submissions/1c5dcbf2-254d-4125-8761-5c154f3b01d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * c + b ^ 3 * a + c ^ 3 * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
