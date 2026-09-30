-- Prove2me | solution 1 for lean_workbook_plus_73364
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:36.557285+00:00
-- url     : https://prove2.me/submissions/96b2a086-044e-47ab-b261-50c23b6eb82d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (1 / 2 : ℝ) ≥ 1 / 4 + 1 / 4 := by
  norm_num
