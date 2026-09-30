-- Prove2me | solution 1 for lean_workbook_plus_74198
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:41.252788+00:00
-- url     : https://prove2.me/submissions/9f184430-7d7c-4df2-90f8-1e3ceb41488a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^400) % 10 = 6 := by
  omega
