-- Prove2me | solution 1 for lean_workbook_plus_42974
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:29.880081+00:00
-- url     : https://prove2.me/submissions/5b921b52-7fcf-48ee-b283-afecda82a75a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 5) (h₂ : a * b + b * c + c * a = 3) : -1 ≤ c ∧ c ≤ 13 / 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
