-- Prove2me | solution 1 for lean_workbook_plus_47751
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:02.202155+00:00
-- url     : https://prove2.me/submissions/4895a5dd-c3f5-4c58-97db-a1e859f715b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) (h : p ^ 3 + q ^ 3 = 2) : p + q ≤ 2 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (p - q), sq_nonneg (p + q)])
