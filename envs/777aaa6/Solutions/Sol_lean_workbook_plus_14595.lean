-- Prove2me | solution 1 for lean_workbook_plus_14595
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:55.618548+00:00
-- url     : https://prove2.me/submissions/f9df51a5-fe2d-40fe-a600-0980f1a4e468

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : b^4 + b^4 + c^4 + a^4 ≥ 4 * a * b^2 * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
