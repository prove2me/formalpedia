-- Prove2me | solution 1 for lean_workbook_plus_51965
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:21.501723+00:00
-- url     : https://prove2.me/submissions/31f34dee-9a3a-45dd-a115-198d211ff091

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a ≥ b ∧ b ≥ c) :
  1 - c ≥ 1 - b ∧ 1 - b ≥ 1 - a := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
