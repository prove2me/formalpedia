-- Prove2me | solution 1 for lean_workbook_plus_40946
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:38.822355+00:00
-- url     : https://prove2.me/submissions/5609cb2f-a92c-4d77-a43c-70bf40beec3b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1): a^4 + b^4 + c^4 ≥ a + b + c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
