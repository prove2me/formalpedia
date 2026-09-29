-- Prove2me | solution 1 for lean_workbook_plus_56664
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:23:39.743892+00:00
-- url     : https://prove2.me/submissions/1dac7e7a-8ce4-4709-a8c3-4ee8cd3915a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : 4 * x * y * z + (y + z) * (z + x) * (x + y) = x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2 := by
  (intros; linarith)
