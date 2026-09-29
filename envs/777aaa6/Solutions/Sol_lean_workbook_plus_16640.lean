-- Prove2me | solution 1 for lean_workbook_plus_16640
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:30.499741+00:00
-- url     : https://prove2.me/submissions/ff286248-3ea9-4d47-a4e1-ad34b9850485

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 3) :
  (a^3 + b^3 + c^3) / 3 ≥ 1 + (a - 1) * (b - 1) * (c - 1) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
