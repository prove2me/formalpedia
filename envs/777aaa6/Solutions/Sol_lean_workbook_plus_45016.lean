-- Prove2me | solution 1 for lean_workbook_plus_45016
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:15:45.135251+00:00
-- url     : https://prove2.me/submissions/ca1c48c5-33a6-490d-9a51-c55ee3a51abb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : -1 < x ∧ x < 0) (hy : 0 < y ∧ y < 1) : x^2 + y^2 + x * y < 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
