-- Prove2me | solution 1 for lean_workbook_plus_47460
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:23.351558+00:00
-- url     : https://prove2.me/submissions/3b9978e2-e4bc-4386-a1ce-c04047a36958

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (2*x+3*y)/(4*x+5*y) + (3*x+2*y)/(5*x+4*y) > 11/10 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
