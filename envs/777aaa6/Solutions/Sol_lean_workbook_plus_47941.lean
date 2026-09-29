-- Prove2me | solution 1 for lean_workbook_plus_47941
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:47.779849+00:00
-- url     : https://prove2.me/submissions/16ea8f3e-fb26-4e4e-9437-19d9ebf5f4ab

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (x + y) * (x - y) ^ 2 + y * (y + z) * (y - z) ^ 2 + z * (z + x) * (z - x) ^ 2 ≥ 0 := by
  (intros; positivity)
