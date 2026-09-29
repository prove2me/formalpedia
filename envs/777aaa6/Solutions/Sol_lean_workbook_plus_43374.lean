-- Prove2me | solution 1 for lean_workbook_plus_43374
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:16:06.928707+00:00
-- url     : https://prove2.me/submissions/15024bbc-7714-49c7-b67e-b41772dcd13e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^2 + y^2) / (x + y) ≥ (x + y) / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
