-- Prove2me | solution 1 for lean_workbook_plus_63964
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:35.219014+00:00
-- url     : https://prove2.me/submissions/140aa870-7f75-486b-a093-bb08e77f150d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / 12 * (x * (3 * x ^ 2 + 2 * y * z) * (x + y - 2 * z) ^ 2 + y * (3 * y ^ 2 + 2 * z * x) * (y + z - 2 * x) ^ 2 + z * (3 * z ^ 2 + 2 * x * y) * (z + x - 2 * y) ^ 2) + 3 / 4 * (x * (x ^ 2 + 4 * y ^ 2) * (x - y) ^ 2 + y * (y ^ 2 + 4 * z ^ 2) * (y - z) ^ 2 + z * (z ^ 2 + 4 * x ^ 2) * (z - x) ^ 2) + 3 * (x * (x - y) ^ 2 * (x + y - z) ^ 2 + y * (y - z) ^ 2 * (y + z - x) ^ 2 + z * (z - x) ^ 2 * (z + x - y) ^ 2) ≥ 0 := by
  (intros; positivity)
