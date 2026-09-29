-- Prove2me | solution 1 for lean_workbook_plus_34870
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:25.03371+00:00
-- url     : https://prove2.me/submissions/69470ed9-a891-47a6-a9e8-2ca52edf69b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a + b = 1) : a^2 + b^2 > a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
