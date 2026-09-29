-- Prove2me | solution 1 for lean_workbook_plus_20593
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:08.369713+00:00
-- url     : https://prove2.me/submissions/b4b01ece-c64e-45af-82fd-8ec70f8570fe

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : (x + 1) * (x + 2) ^ 2 * (x + 3) ≥ -1 / 4 := by
  nlinarith [sq_nonneg ((x+2)^2-1/2)]
