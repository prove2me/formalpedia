-- Prove2me | solution 1 for lean_workbook_plus_36888
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:30.065296+00:00
-- url     : https://prove2.me/submissions/7f27efb9-969f-414d-9388-6152d0e8d65b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c : ℝ) : a ^ 4 + c ^ 4 ≥ a ^ 3 * c + a * c ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (c), sq_nonneg (a - c), sq_nonneg (a + c)])
