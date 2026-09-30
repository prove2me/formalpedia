-- Prove2me | solution 1 for lean_workbook_plus_21675
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:57.946945+00:00
-- url     : https://prove2.me/submissions/9d87d0d4-152d-4471-91e6-8b7e8b15cf02

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (3^115) % 28 = 3 := by
  norm_num
