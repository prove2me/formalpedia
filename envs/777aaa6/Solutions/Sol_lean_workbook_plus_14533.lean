-- Prove2me | solution 1 for lean_workbook_plus_14533
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:49.067168+00:00
-- url     : https://prove2.me/submissions/f8ff657b-588a-4707-b5c0-5033bd96abee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + x * y) * (y + z + y * z) * (z + x + z * x) ≥ x * y * z * (x + 2) * (y + 2) * (z + 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz])
