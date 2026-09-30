-- Prove2me | solution 1 for lean_workbook_plus_56596
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:44.100302+00:00
-- url     : https://prove2.me/submissions/a10f5a3a-6ccd-42b1-bd41-5089a8be3896

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : √(5^2) = 5 := by
  simp
