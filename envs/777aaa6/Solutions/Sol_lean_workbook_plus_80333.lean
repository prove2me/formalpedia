-- Prove2me | solution 1 for lean_workbook_plus_80333
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:00.854104+00:00
-- url     : https://prove2.me/submissions/ae56efbf-e00b-4de3-8174-5c82537b4ada

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^116 < 10^35 := by
  norm_num
