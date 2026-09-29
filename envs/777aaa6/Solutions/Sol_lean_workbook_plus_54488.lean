-- Prove2me | solution 1 for lean_workbook_plus_54488
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:02.551771+00:00
-- url     : https://prove2.me/submissions/92687b46-cf18-4213-a70b-a4c187eba344

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 = (a - b) ^ 2 ∧ (a - b) ^ 2 ≥ 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
