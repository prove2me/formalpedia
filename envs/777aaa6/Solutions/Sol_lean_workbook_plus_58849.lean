-- Prove2me | solution 1 for lean_workbook_plus_58849
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:24.470361+00:00
-- url     : https://prove2.me/submissions/673fac63-177f-430e-bed2-25cfa2440378

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p1 p2 : ℝ) (h1 : p1 = 1000) (h2 : p2 = 1270) : (p2 - p1) / p1 * 100 = 27 := by
  (intros; field_simp; nlinarith [sq_nonneg (p1), sq_nonneg (p2), sq_nonneg (p1 - p2), sq_nonneg (p1 + p2)])
