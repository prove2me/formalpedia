-- Prove2me | solution 1 for lean_workbook_plus_69113
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:13.424038+00:00
-- url     : https://prove2.me/submissions/44f6737a-3d01-4667-9a2b-e1dd813be3fe

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
    x + y + z ≤ 2 + x * y * z ↔ x * (1 - y * z) + y + z ≤ 2 := by
  constructor <;> intro h <;> nlinarith [h]

#print axioms solution
