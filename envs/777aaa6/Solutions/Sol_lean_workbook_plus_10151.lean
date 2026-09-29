-- Prove2me | solution 1 for lean_workbook_plus_10151
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:35.873838+00:00
-- url     : https://prove2.me/submissions/2de882c2-2e34-40e0-b224-997f227eb97c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : a + b + c = 0) (h2 : a^3 + b^3 + c^3 = 0) : a * b * c = 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
