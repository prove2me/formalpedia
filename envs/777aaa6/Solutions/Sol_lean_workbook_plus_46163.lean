-- Prove2me | solution 1 for lean_workbook_plus_46163
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:39.256273+00:00
-- url     : https://prove2.me/submissions/02f5e7d0-0149-4c59-8dab-1cd7f46303b3

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : √1 = 1 := by
  norm_num
