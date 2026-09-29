-- Prove2me | solution 1 for lean_workbook_plus_81873
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:11.934439+00:00
-- url     : https://prove2.me/submissions/3a3c4916-746e-4e63-864b-073500c7e597

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ≤ y + z) : x / (1 + x) ≤ y / (1 + y) + z / (1 + z) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
