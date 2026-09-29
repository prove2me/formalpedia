-- Prove2me | solution 1 for lean_workbook_plus_61453
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:31:50.681997+00:00
-- url     : https://prove2.me/submissions/b1d5d779-e077-4ae0-8c2c-956b4c16a336

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x / (x + 1) + y / (3 * y + 1)) ≥ (x + y) / (3 * (x + y) + 1) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
