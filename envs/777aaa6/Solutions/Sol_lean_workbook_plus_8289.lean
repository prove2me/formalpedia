-- Prove2me | solution 1 for lean_workbook_plus_8289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:17.976288+00:00
-- url     : https://prove2.me/submissions/5eb2a036-dfa1-43a2-80e1-e97eb2f15c3f

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 ^ 12 ≡ 1 [ZMOD 130] := by
  decide
