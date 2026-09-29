-- Prove2me | solution 1 for lean_workbook_plus_26038
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:29.063785+00:00
-- url     : https://prove2.me/submissions/58a541ee-c18f-45b6-b028-ba843c758512

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≤ 2 * (x^2 / (y + z) + y^2 / (x + z) + z^2 / (x + y)) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
