-- Prove2me | solution 1 for lean_workbook_plus_9610
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:43.855113+00:00
-- url     : https://prove2.me/submissions/fc3302b3-1eef-4461-b24c-c87b298b2568

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a * (a + 1) ^ 2 + b * (b + 1) ^ 2 = 8) : a + b ≤ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
