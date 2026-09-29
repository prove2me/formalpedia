-- Prove2me | solution 1 for lean_workbook_plus_13424
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:55.656198+00:00
-- url     : https://prove2.me/submissions/92bbddda-6081-4b54-ad8e-b7e8f89d3c5b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
