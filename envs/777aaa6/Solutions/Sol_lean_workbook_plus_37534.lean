-- Prove2me | solution 1 for lean_workbook_plus_37534
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:37.363159+00:00
-- url     : https://prove2.me/submissions/f107e07f-9f9e-43d9-90b7-964c762c4c08

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 4 * (a ^ 2 + b ^ 2) ≥ 8 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
