-- Prove2me | solution 1 for lean_workbook_plus_10394
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:40:47.826869+00:00
-- url     : https://prove2.me/submissions/5d2353c4-b8db-4e07-9a30-9dc11d657d8a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^2 + b^2 ≥ (a + b)^2 / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
