-- Prove2me | solution 1 for lean_workbook_plus_46512
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:05.020913+00:00
-- url     : https://prove2.me/submissions/bcad637b-8164-45b8-9c4c-7d666b5ebeec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + a * b + b * c ≥ 1 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
