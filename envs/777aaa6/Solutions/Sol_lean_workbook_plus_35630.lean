-- Prove2me | solution 1 for lean_workbook_plus_35630
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:29.451986+00:00
-- url     : https://prove2.me/submissions/be180383-0859-495f-960b-0c334fac8426

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (300 / 60) * 70 = 350 := by
  norm_num
