-- Prove2me | solution 1 for lean_workbook_plus_41266
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:30.48156+00:00
-- url     : https://prove2.me/submissions/56100435-67d6-483e-a385-1ab4dad57123

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^3 + y^3 + 2 * z^3 ≥ y * z * (y + z) + x * z * (z + x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
