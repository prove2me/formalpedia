-- Prove2me | solution 1 for lean_workbook_plus_58693
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:39.628285+00:00
-- url     : https://prove2.me/submissions/cc944a53-493a-4a03-a1eb-b99ccb354159

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : 0 < x + y) (h : (x - y) * (x - 1) ≤ 0) : (x + 2 * y) / (y + 2 * x) ≥ (y + 2 * x * y) / (x + 2 * x * y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
