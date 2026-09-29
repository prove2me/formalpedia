-- Prove2me | solution 1 for lean_workbook_plus_4643
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:11.574846+00:00
-- url     : https://prove2.me/submissions/89a1a953-b66d-4452-ba84-b2dd02ed7be0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a^2 * (a + 1) + b^2 * (b + 1) = 4) : a + b ≤ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
