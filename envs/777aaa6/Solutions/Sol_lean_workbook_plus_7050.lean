-- Prove2me | solution 1 for lean_workbook_plus_7050
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:13.522636+00:00
-- url     : https://prove2.me/submissions/77c30166-c792-4628-9c7a-825d8810de7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c ≥ 3) : a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c ≥ 6 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
