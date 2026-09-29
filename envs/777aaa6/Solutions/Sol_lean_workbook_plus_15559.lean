-- Prove2me | solution 1 for lean_workbook_plus_15559
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:23.10224+00:00
-- url     : https://prove2.me/submissions/1ecdadfe-1f86-4c0b-b0cb-4805e6f4d27b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y + 2)⁻¹ + (x + 1)⁻¹ * (y + 1)⁻¹ ≤ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_nonneg hx hy])
