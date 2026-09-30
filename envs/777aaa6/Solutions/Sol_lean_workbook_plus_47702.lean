-- Prove2me | solution 1 for lean_workbook_plus_47702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:08.816905+00:00
-- url     : https://prove2.me/submissions/3062033e-0ae5-423e-9271-95788cb3c37b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 ^ 10 ≡ 1 [ZMOD 11] := by
  decide
