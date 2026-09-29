-- Prove2me | solution 1 for lean_workbook_plus_79425
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:10.117977+00:00
-- url     : https://prove2.me/submissions/d7633715-b046-43dd-b9c6-7e19e753b6a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a ^ 4 + b ^ 4 ≥ (1 / 8) * (a + b) ^ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
