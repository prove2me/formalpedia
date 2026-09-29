-- Prove2me | solution 1 for lean_workbook_plus_66893
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:32.526706+00:00
-- url     : https://prove2.me/submissions/114a1137-d284-432b-b6e2-37d197351f85

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) : a + b ≤ c + a ∧ c + a ≤ b + c := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
