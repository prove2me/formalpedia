-- Prove2me | solution 1 for lean_workbook_plus_4642
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:20.644367+00:00
-- url     : https://prove2.me/submissions/0c4ca917-ee80-4206-857a-c18aa3e33ae2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  32 * 1296 * 126 = 5225472 := by
  norm_num
