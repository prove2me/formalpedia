-- Prove2me | solution 1 for lean_workbook_plus_59650
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:28.078661+00:00
-- url     : https://prove2.me/submissions/3042a9e8-1575-460e-b95d-23a3bb080f3a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 4 + (3 * 4) / 2 - 2 = 8 := by
  norm_num
