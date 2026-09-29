-- Prove2me | solution 1 for lean_workbook_plus_36609
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:25.099667+00:00
-- url     : https://prove2.me/submissions/b6e061a2-c272-4bb7-bb85-bb1a6cdc5a7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a ^ 2 + b ^ 2 + a * b ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
