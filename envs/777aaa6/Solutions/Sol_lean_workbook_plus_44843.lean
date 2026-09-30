-- Prove2me | solution 1 for lean_workbook_plus_44843
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:41.472051+00:00
-- url     : https://prove2.me/submissions/10f94334-2576-461d-9bcc-204ca700c3ea

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 % 2 = 1 := by
  norm_num
