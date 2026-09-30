-- Prove2me | solution 1 for lean_workbook_plus_81296
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:51:13.088628+00:00
-- url     : https://prove2.me/submissions/793ab1e5-c3b3-48dd-9485-79738be505f1

import Mathlib

theorem solution (x y z : ℕ) (hx : x + y + z = 6) : x * y^2 * z^3 ≤ 108 := by
  have hxb : x ≤ 6 := by omega
  have hyb : y ≤ 6 := by omega
  have hz : z = 6 - x - y := by omega
  subst z
  interval_cases x <;> interval_cases y <;> norm_num
