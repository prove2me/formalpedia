-- Prove2me | solution 1 for lean_workbook_plus_23699
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:55.969711+00:00
-- url     : https://prove2.me/submissions/fffe3c6b-0fec-4fba-a73c-6abbf006d7d6

import Mathlib
set_option autoImplicit false

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b) ^ 2 * (c + d) ^ 2 + (a + c) ^ 2 * (b + d) ^ 2 + (a + d) ^ 2 * (b + c) ^ 2 >= 3 * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)   := by
  have hgap :
      (a + b) ^ 2 * (c + d) ^ 2 + (a + c) ^ 2 * (b + d) ^ 2 +
        (a + d) ^ 2 * (b + c) ^ 2 -
        3 * (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) =
      (((a * b + c * d) - (a * c + b * d)) ^ 2 +
        ((a * c + b * d) - (a * d + b * c)) ^ 2 +
        ((a * d + b * c) - (a * b + c * d)) ^ 2) / 2 +
        (a * b - c * d) ^ 2 + (a * c - b * d) ^ 2 + (a * d - b * c) ^ 2 := by
    ring
  apply sub_nonneg.mp
  rw [hgap]
  positivity

#print axioms solution
