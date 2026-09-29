-- Prove2me | solution 1 for lean_workbook_plus_41962
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:45.446763+00:00
-- url     : https://prove2.me/submissions/429ce078-7ddc-45d4-abd6-d079bdf781f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) : 1/x + 1/y ≥ 4/(x + y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
