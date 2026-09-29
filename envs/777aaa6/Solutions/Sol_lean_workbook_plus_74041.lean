-- Prove2me | solution 1 for lean_workbook_plus_74041
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:14.301854+00:00
-- url     : https://prove2.me/submissions/458f6814-b97c-4f9e-ba5c-3f1ff571bf42

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x + y) / (1 + x + y) < x / (1 + x) + y / (1 + y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
