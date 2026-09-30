-- Prove2me | solution 1 for lean_workbook_plus_3399
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:12.705002+00:00
-- url     : https://prove2.me/submissions/2cc08c43-9b96-4b3b-a1a0-e852154c31bc

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7^7 * 7^7 > (3^3 * 4^4)^3 := by
  norm_num
