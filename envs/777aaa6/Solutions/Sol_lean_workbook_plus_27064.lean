-- Prove2me | solution 1 for lean_workbook_plus_27064
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:44.351277+00:00
-- url     : https://prove2.me/submissions/7f4a3ea1-53ea-4704-974e-d897e343db11

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (2004 / 2) = 1002 := by
  norm_num
