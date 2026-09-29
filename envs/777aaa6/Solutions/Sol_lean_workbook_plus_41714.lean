-- Prove2me | solution 1 for lean_workbook_plus_41714
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:30:07.330519+00:00
-- url     : https://prove2.me/submissions/a8f9aa91-3728-4dda-b0bc-951aa5d1bf4e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx:0 ≤ x) (hy:0 ≤ y) (hz:0 ≤ z) : x * (x + y) ^ 2 + 2 * z ^ 3 ≥ 2 * x * (y * z + z ^ 2 + x * y) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
