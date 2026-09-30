-- Prove2me | solution 1 for lean_workbook_plus_60324
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:02.0917+00:00
-- url     : https://prove2.me/submissions/91b99fdf-4b4b-4e5c-94d7-9c40df13fb1e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^1 - 2^0 = 1 := by
  norm_num
