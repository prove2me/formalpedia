-- Prove2me | solution 1 for lean_workbook_plus_39574
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:31.215564+00:00
-- url     : https://prove2.me/submissions/019ecdf9-e6c0-4b4f-b5e4-e35ddce8ff39

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h : x ≥ y ∧ y ≥ z ∧ z > 0) : x^2*y + y^2*z + z^2*x ≥ x^2*z + y^2*x + z^2*y := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
