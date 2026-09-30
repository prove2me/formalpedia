-- Prove2me | solution 1 for lean_workbook_plus_47497
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:30.8356+00:00
-- url     : https://prove2.me/submissions/708c5ad8-41bf-43a4-81d6-93829aa60d6a

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 6) (h₂ : x*y + y*z + z*x = 11) (h₃ : x*y*z = 6) : x^5 + y^5 + z^5 = 276   := by
  calc
    x ^ 5 + y ^ 5 + z ^ 5 =
        (x + y + z) ^ 5 - 5 * (x + y + z) ^ 3 * (x * y + y * z + z * x) +
        5 * (x + y + z) * (x * y + y * z + z * x) ^ 2 +
        5 * (x + y + z) ^ 2 * (x * y * z) -
        5 * (x * y + y * z + z * x) * (x * y * z) := by ring
    _ = 276 := by rw [h₁, h₂, h₃]; norm_num

#print axioms solution
