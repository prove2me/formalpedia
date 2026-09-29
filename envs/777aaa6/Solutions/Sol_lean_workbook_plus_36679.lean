-- Prove2me | solution 1 for lean_workbook_plus_36679
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:17.783306+00:00
-- url     : https://prove2.me/submissions/0abaf1e6-364f-4083-873b-b8b26c4e198f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a ^ 4 + 6 * a ^ 2 * b ^ 2 + b ^ 4 ≥ 4 * a ^ 3 * b + 4 * a * b ^ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
