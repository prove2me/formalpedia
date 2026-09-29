-- Prove2me | solution 1 for lean_workbook_plus_15480
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:14.015231+00:00
-- url     : https://prove2.me/submissions/0a77034c-c834-4775-bf0e-e4701dfc9d49

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^2 + y^2 > 2) : x^3 + y^3 > 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
