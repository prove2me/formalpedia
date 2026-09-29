-- Prove2me | solution 1 for lean_workbook_plus_62481
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:31.113283+00:00
-- url     : https://prove2.me/submissions/abe6dec5-30ab-458c-a38f-1765389068cf

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a > b) : a > (a + b) / 2 ∧ (a + b) / 2 > b := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
