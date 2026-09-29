-- Prove2me | solution 1 for lean_workbook_plus_65961
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:50:01.639214+00:00
-- url     : https://prove2.me/submissions/aa3b72a5-20ef-47c6-9963-2b61e8179435

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / y ^ 2 + y / x ^ 2) ≥ (1 / x + 1 / y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
