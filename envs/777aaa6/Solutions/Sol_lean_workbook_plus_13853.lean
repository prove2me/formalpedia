-- Prove2me | solution 1 for lean_workbook_plus_13853
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:33.449822+00:00
-- url     : https://prove2.me/submissions/56925aee-6cfa-4c77-b698-487851f7e07d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∨ x ≥ z ∧ z ≥ y) (hx : 0 < x ∧ 0 < y ∧ 0 < z) : x^3 + y^3 + z^3 + 2 * (x^2 * y + y^2 * z + z^2 * x) ≥ 3 * (x^2 * y + y^2 * z + z^2 * x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
