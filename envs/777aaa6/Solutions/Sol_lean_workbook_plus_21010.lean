-- Prove2me | solution 1 for lean_workbook_plus_21010
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:44.337549+00:00
-- url     : https://prove2.me/submissions/3dc0978a-139c-4a85-b29a-ba221b2d7afc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a + b - 1 < a * b) (h : a * b < 1) : a < 1 ∧ b < 1 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
