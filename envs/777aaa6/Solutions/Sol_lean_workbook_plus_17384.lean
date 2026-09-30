-- Prove2me | solution 1 for lean_workbook_plus_17384
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:15:45.953637+00:00
-- url     : https://prove2.me/submissions/5e9bd1c7-8d20-4c96-bf0b-8dc3869bbb6f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 8 * 7 = 56 := by
  norm_num
