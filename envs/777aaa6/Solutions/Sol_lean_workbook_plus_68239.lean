-- Prove2me | solution 1 for lean_workbook_plus_68239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:57.851593+00:00
-- url     : https://prove2.me/submissions/d0c846ca-b3c2-4766-94f5-a57aa5741a7b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b ≥ 1) : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≥ 2 / (1 + a * b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
