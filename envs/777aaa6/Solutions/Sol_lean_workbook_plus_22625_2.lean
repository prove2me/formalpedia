-- Prove2me | solution 2 for lean_workbook_plus_22625
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:35.618451+00:00
-- url     : https://prove2.me/submissions/4873045e-9efe-4aa7-9f5c-e7bea46a0695

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b x z : ℝ) : a * x = z + b ∧ b * z = x + a → (a - 1) * x + (b - 1) * z = a + b := by
  (intros; linarith)
