-- Prove2me | solution 1 for lean_workbook_plus_1369
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:17.06143+00:00
-- url     : https://prove2.me/submissions/46c96477-f950-497a-8b4e-32bcde38212e

import Mathlib
set_option autoImplicit false

theorem solution {m n z x : ℝ}
 (hm : 0 < m)
 (hn : 0 < n)
 (hz : 0 < z)
 (hx : 0 < x) :
 (m * z + n * x) / (m + n) ≥ (m + n) / (m / z + n / x)   := by
  have hs : 0 < m + n := add_pos hm hn
  have ht : 0 < m / z + n / x := add_pos (div_pos hm hz) (div_pos hn hx)
  have hp : 0 < z * x := mul_pos hz hx
  apply (div_le_div_iff₀ ht hs).mpr
  apply (mul_le_mul_iff_right₀ hp).mp
  have he : ((m * z + n * x) * (m / z + n / x) - (m + n) * (m + n)) * (z * x) =
      m * n * (z - x) ^ 2 := by
    field_simp [ne_of_gt hz, ne_of_gt hx]
    ring
  have hq := mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hn)) (sq_nonneg (z - x))
  nlinarith only [he, hq]

#print axioms solution
