-- Prove2me | solution 1 for lean_workbook_plus_6169
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:50:06.697245+00:00
-- url     : https://prove2.me/submissions/8cc22c09-2317-4c10-8799-e73322a9bb06

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a = 25^12) (hb : b = 16^14) (hc : c = 11^16) : b > a ∧ a > c := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
