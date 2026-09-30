-- Prove2me | solution 1 for lean_workbook_plus_60546
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:11.006451+00:00
-- url     : https://prove2.me/submissions/87614324-90f6-4272-b395-c966edf095d2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 12 ≡ 7 [ZMOD 5] := by
  decide
