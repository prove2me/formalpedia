-- Prove2me | solution 1 for lean_workbook_plus_3907
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:04.342343+00:00
-- url     : https://prove2.me/submissions/b943e46b-182c-40e5-ab18-2379b1e6f17f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 * 1^2 + 1 ≤ 3^1 := by
  norm_num
