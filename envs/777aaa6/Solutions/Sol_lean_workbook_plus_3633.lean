-- Prove2me | solution 1 for lean_workbook_plus_3633
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:08:21.263938+00:00
-- url     : https://prove2.me/submissions/57ed2700-16dc-470f-abad-0310e57bddef

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 6) (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 40) (h₃ : a ^ 3 + b ^ 3 + c ^ 3 = 200) : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) = 40 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
