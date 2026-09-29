-- Prove2me | solution 1 for lean_workbook_plus_9103
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:48.562427+00:00
-- url     : https://prove2.me/submissions/2c46433f-5c6f-4c67-ac5f-ba3c1021f9e3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 1 ≤ x * y) :
  1 / (1 + x^2) + 1 / (1 + y^2) ≥ 2 / (1 + x * y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
