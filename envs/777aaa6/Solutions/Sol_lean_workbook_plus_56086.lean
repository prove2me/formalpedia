-- Prove2me | solution 1 for lean_workbook_plus_56086
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:56.12328+00:00
-- url     : https://prove2.me/submissions/db1694b0-26fb-492b-934c-db5a28ec7e5e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 999 + 10 = 1009 := by
  norm_num
