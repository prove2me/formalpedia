-- Prove2me | solution 1 for lean_workbook_plus_34595
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:43:02.741734+00:00
-- url     : https://prove2.me/submissions/6191c611-8777-435d-a18d-d0da933ca44a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2+b^2+c^2)*(1+1+1) ≥ (a+b+c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
