-- Prove2me | solution 1 for lean_workbook_plus_46663
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:17.389974+00:00
-- url     : https://prove2.me/submissions/989fd438-a807-430d-b0c1-4d9cfd030252

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (2 : ℝ) > 1 := by
  norm_num
