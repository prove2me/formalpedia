-- Prove2me | solution 1 for lean_workbook_plus_5167
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:41.839884+00:00
-- url     : https://prove2.me/submissions/e84cf924-55d7-4cc4-95fb-bfae74588b45

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 12 ≡ 5 [ZMOD 7] := by
  decide
