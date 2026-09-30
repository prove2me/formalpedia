-- Prove2me | solution 1 for lean_workbook_plus_34873
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:50.519327+00:00
-- url     : https://prove2.me/submissions/fe361aea-9761-43dd-aba6-cffe15ce735b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 43 * 2 - 1 - 5 = 80 := by
  norm_num
