-- Prove2me | solution 1 for lean_workbook_plus_15662
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:33.684049+00:00
-- url     : https://prove2.me/submissions/4ecc9ecf-06a4-430f-85d0-23344d5ff004

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
