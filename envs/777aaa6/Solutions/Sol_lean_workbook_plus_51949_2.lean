-- Prove2me | solution 2 for lean_workbook_plus_51949
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:11:57.142962+00:00
-- url     : https://prove2.me/submissions/94645e34-1f4c-45ca-bc19-8f67094dce85

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) (h : x^2 + y^2 ≤ x + y) : x + y ≤ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 1), sq_nonneg (y - 1)]
