-- Prove2me | solution 1 for lean_workbook_plus_38471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:32.592929+00:00
-- url     : https://prove2.me/submissions/1211805e-fde5-4af2-9cd7-8fea8737a762

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (5 * 7^34 : ℝ) > 1.2 * 10^29 := by
  norm_num
