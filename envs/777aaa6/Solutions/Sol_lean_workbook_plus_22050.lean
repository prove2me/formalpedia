-- Prove2me | solution 1 for lean_workbook_plus_22050
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:09.161594+00:00
-- url     : https://prove2.me/submissions/e00bf0de-2b5b-4dc8-8116-b0b4674cd29b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 + y^3 + z^3 ≥ (x^4 + y^4 + z^4) / (x + y + z) + 2 * x * y * z := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
