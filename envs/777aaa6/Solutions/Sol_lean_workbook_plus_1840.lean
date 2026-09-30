-- Prove2me | solution 1 for lean_workbook_plus_1840
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:44.215629+00:00
-- url     : https://prove2.me/submissions/9b795fb7-e600-481b-be2f-d26a7c9e5306

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1547 % 13 = 0 := by
  norm_num
