-- Prove2me | solution 1 for lean_workbook_plus_25748
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:50.853646+00:00
-- url     : https://prove2.me/submissions/573f1d36-31a8-470d-bcee-9f7527e3a360

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (b c : ℝ) : b ^ 2 + 4 * c ^ 2 - 4 * b * c ≥ 0 := by
  nlinarith [sq_nonneg (b-2*c)]
