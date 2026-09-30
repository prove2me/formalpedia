-- Prove2me | solution 1 for lean_workbook_plus_51000
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:05.347479+00:00
-- url     : https://prove2.me/submissions/7ad11943-1583-490e-869e-7440be3ec8ca

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5 - (-3) = 8 := by
  norm_num
