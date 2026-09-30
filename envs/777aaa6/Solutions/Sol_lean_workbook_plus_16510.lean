-- Prove2me | solution 1 for lean_workbook_plus_16510
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:24.788147+00:00
-- url     : https://prove2.me/submissions/48e73765-13ae-4814-b0ac-74ab73cf51cb

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 105 = 5^2 + 4 * (5^2 - 5) := by
  norm_num
