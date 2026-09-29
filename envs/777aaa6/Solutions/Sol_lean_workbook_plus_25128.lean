-- Prove2me | solution 1 for lean_workbook_plus_25128
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:10.455049+00:00
-- url     : https://prove2.me/submissions/d0505c41-1d50-4c0b-ae2e-c4830a822da1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : (b + c) ^ 4 ≤ 16 * (b ^ 4 - b ^ 2 * c ^ 2 + c ^ 4) := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
