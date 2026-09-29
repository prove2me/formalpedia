-- Prove2me | solution 1 for lean_workbook_plus_60853
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:45.091509+00:00
-- url     : https://prove2.me/submissions/86f46f5c-1373-4cf7-ae10-bd699b5d83f2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a * b = 0) (h₂ : a + b = 0) : a = 0 ∧ b = 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
