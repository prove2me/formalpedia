-- Prove2me | solution 1 for lean_workbook_plus_81115
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:12.204878+00:00
-- url     : https://prove2.me/submissions/c3c1eadb-95e7-4c30-93cd-665e386b1ae0

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 ^ 10 ≡ 1 [ZMOD 11] := by
  decide
