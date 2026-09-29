-- Prove2me | solution 1 for lean_workbook_plus_79241
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:18:40.270011+00:00
-- url     : https://prove2.me/submissions/7f45d8c9-85f3-4615-9631-16408e6c3882

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 + y^3 ≥ x * y * (x + y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
