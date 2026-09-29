-- Prove2me | solution 1 for lean_workbook_plus_17772
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:02.135836+00:00
-- url     : https://prove2.me/submissions/79e44c57-e1d9-4428-998c-db70a5af6329

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y + x*y = 1) : x*y + 1/(x*y) - y/x - x/y = 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
