-- Prove2me | solution 1 for lean_workbook_plus_80351
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:10.509519+00:00
-- url     : https://prove2.me/submissions/aacb1e31-78f9-46ae-a6df-e31e4a56a2ab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) : (b + c) ^ 2 ≥ 4 * b * c := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
