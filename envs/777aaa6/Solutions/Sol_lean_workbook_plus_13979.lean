-- Prove2me | solution 1 for lean_workbook_plus_13979
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:13.731051+00:00
-- url     : https://prove2.me/submissions/b1cb19d2-7d84-4def-82e8-85586e6cd2e2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 6 + 4 + 25 + 2020 = 2055 := by
  norm_num
