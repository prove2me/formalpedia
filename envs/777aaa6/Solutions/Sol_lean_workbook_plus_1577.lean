-- Prove2me | solution 1 for lean_workbook_plus_1577
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:19.333327+00:00
-- url     : https://prove2.me/submissions/7df929aa-139b-4cf5-ac2f-f8bc65b96f70

import Mathlib
set_option autoImplicit false

theorem solution (z : ℝ) (hz : -1/3 ≤ z) : z / (z^2 + 1) ≤ 1/2   := by
  apply (div_le_iff₀ (show 0 < z ^ 2 + 1 by positivity)).mpr
  nlinarith [sq_nonneg (z - 1)]

#print axioms solution
