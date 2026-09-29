-- Prove2me | solution 1 for lean_workbook_plus_19397
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:15.890642+00:00
-- url     : https://prove2.me/submissions/99840c05-4af1-401c-914d-6eb2f19e667e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x^2 + y^2 + z^2)^2 + x^3*y + y^3*z + z^3*x - (2/3)*(x + y + z)*(x^3 + y^3 + z^3) - (2/3)*(x + y + z)*(x^2*y + y^2*z + z^2*x) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz])
