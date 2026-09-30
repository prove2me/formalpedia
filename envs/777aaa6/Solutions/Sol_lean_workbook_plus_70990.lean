-- Prove2me | solution 1 for lean_workbook_plus_70990
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:14.669666+00:00
-- url     : https://prove2.me/submissions/f0c3d8f1-4f30-4a6c-8835-4e8e446977b1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 65 * 66 * 67 * 68 > 16 := by
  norm_num
