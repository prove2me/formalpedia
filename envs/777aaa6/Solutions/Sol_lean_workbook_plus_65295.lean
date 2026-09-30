-- Prove2me | solution 1 for lean_workbook_plus_65295
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:00.847349+00:00
-- url     : https://prove2.me/submissions/9ebc76c5-a24d-47c3-894b-b646f1cc148d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 32768^25 = 2^375 := by
  omega
