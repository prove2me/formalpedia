-- Prove2me | solution 1 for lean_workbook_plus_25915
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:13.23116+00:00
-- url     : https://prove2.me/submissions/1196d4be-40eb-4847-bd89-ece3a99cd12c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a * b * c ≠ 0) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
