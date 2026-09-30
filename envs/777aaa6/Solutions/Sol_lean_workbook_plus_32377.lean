-- Prove2me | solution 1 for lean_workbook_plus_32377
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:52.202625+00:00
-- url     : https://prove2.me/submissions/0b00875b-f3ae-4497-84ab-3a5c384c4b05

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (2^33) > 1000000000 := by
  norm_num
