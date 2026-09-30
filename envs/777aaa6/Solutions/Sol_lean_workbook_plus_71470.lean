-- Prove2me | solution 1 for lean_workbook_plus_71470
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:32.228943+00:00
-- url     : https://prove2.me/submissions/46064c97-cb52-4d04-994f-dbc2e37c080b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 55 + 1 ≡ 0 [ZMOD 11] := by
  decide
