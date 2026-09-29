-- Prove2me | solution 1 for lean_workbook_plus_68493
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:28.946542+00:00
-- url     : https://prove2.me/submissions/7305e65c-da8b-43c2-aca2-4f36154b2265

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ (a + b + c) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
