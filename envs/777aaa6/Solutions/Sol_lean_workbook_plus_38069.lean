-- Prove2me | solution 1 for lean_workbook_plus_38069
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:56.693565+00:00
-- url     : https://prove2.me/submissions/26a7a3de-01fd-4def-ae69-c197d9f5b84f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (17^3 / 16^3 : ℝ) > 1 := by
  norm_num
