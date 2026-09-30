-- Prove2me | solution 1 for lean_workbook_plus_31419
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:02.639786+00:00
-- url     : https://prove2.me/submissions/20dbd62f-c9af-4814-90ab-c141ce2acb6b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  1547 % 7 = 0 := by
  norm_num
