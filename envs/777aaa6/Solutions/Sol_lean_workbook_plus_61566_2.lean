-- Prove2me | solution 2 for lean_workbook_plus_61566
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:39.880249+00:00
-- url     : https://prove2.me/submissions/a5bccecb-c7fc-466e-9120-4b6e85d5d2b7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h1 : x + y ≥ 1) (h2 : |x*y| ≤ 2) : x^3 + y^3 ≥ -7 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
