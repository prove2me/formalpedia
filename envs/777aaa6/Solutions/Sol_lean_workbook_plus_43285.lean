-- Prove2me | solution 1 for lean_workbook_plus_43285
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:43.64028+00:00
-- url     : https://prove2.me/submissions/a77a226b-5d16-47b3-9648-abfd560b9f84

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : 11 * (a + b) ^ 2 + 22 * c ^ 2 ≥ (3 * a + 3 * b + 2 * c) ^ 2 := by
  nlinarith [sq_nonneg (a+b-3*c)]
