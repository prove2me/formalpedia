-- Prove2me | solution 1 for lean_workbook_plus_21112
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:28.372654+00:00
-- url     : https://prove2.me/submissions/1a1d820c-2557-4b5c-9782-d25080ed44f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) :
  (1 - x) * (1 - y) ≤ ((2 - (x + y)) / 2)^2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
