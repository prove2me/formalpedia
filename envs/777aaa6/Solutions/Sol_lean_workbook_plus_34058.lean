-- Prove2me | solution 1 for lean_workbook_plus_34058
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:04.226624+00:00
-- url     : https://prove2.me/submissions/cbdeb19f-c841-4896-9033-cd96744b27fb

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2) : 3 * (x + y + z) ≤ x*y*z + 10   := by
  have hxy' : (2 : ℝ) * 2 ≤ x * y := mul_le_mul hx hy (by norm_num) (by linarith)
  have hxy : 4 ≤ x * y := by nlinarith only [hxy']
  have hp : 0 ≤ (x * y - 3) * (z - 2) :=
    mul_nonneg (by linarith [hxy]) (by linarith [hz])
  have hq : 0 ≤ (x - 2) * (y - 2) :=
    mul_nonneg (by linarith [hx]) (by linarith [hy])
  nlinarith only [hp, hq, hx, hy]

#print axioms solution
