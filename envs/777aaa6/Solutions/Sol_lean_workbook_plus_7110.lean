-- Prove2me | solution 1 for lean_workbook_plus_7110
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:35.475401+00:00
-- url     : https://prove2.me/submissions/88ccf6ba-b29a-4d6a-80da-f41688e3c3d0

import Mathlib
set_option autoImplicit false

theorem solution {m n x y : ℝ} (hm : 0 < m) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
  (m * x + n * y) / (m + n) ≥ (m + n) / (m / x + n / y)   := by
  have hs : 0 < m + n := add_pos hm hn
  have ht : 0 < m / x + n / y := add_pos (div_pos hm hx) (div_pos hn hy)
  apply (div_le_div_iff₀ ht hs).2
  have hxy : 0 < x * y := mul_pos hx hy
  apply (mul_le_mul_iff_right₀ hxy).mp
  have hid : ((m * x + n * y) * (m / x + n / y) - (m + n) * (m + n)) *
      (x * y) = m * n * (x - y) ^ 2 := by
    field_simp [ne_of_gt hx, ne_of_gt hy]
    ring
  have hp := mul_nonneg (mul_nonneg (le_of_lt hm) (le_of_lt hn)) (sq_nonneg (x - y))
  nlinarith only [hid, hp]

#print axioms solution
