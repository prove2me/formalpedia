-- Prove2me | solution 1 for lean_workbook_plus_46985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:42.242023+00:00
-- url     : https://prove2.me/submissions/4a339126-3ba2-491c-85c9-99c60c38ca11

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 77 = 7 * 11 := by
  norm_num
