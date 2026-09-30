-- Prove2me | solution 1 for lean_workbook_plus_11941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:15.597654+00:00
-- url     : https://prove2.me/submissions/3258dc34-3ce8-457e-b938-d74972972f23

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  3456 = 2^7 * 3^3 := by
  norm_num
