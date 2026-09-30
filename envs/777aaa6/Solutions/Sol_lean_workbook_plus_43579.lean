-- Prove2me | solution 1 for lean_workbook_plus_43579
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:57.299005+00:00
-- url     : https://prove2.me/submissions/33bfde15-3010-4d98-951b-280f47c28452

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 131^5 > 21^8 := by
  norm_num
