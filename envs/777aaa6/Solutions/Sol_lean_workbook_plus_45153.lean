-- Prove2me | solution 1 for lean_workbook_plus_45153
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:49:47.300873+00:00
-- url     : https://prove2.me/submissions/21c64772-ca1a-4f0d-8b10-b23451e5e8ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^4 + y^4 + z^4) + 2 * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ≥ (2 * (x^3 * y + y^3 * z + z^3 * x)) + (x * y^3 + y * z^3 + z * x^3) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
