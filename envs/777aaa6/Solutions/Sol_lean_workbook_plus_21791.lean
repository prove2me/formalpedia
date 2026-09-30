-- Prove2me | solution 1 for lean_workbook_plus_21791
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:13.759984+00:00
-- url     : https://prove2.me/submissions/2971b2d9-7961-4ffb-93bb-58d58ada73d6

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^14 = 16384 → 2^15 = 32768 := by
  norm_num
