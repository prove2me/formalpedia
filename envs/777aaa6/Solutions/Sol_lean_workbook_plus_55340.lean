-- Prove2me | solution 1 for lean_workbook_plus_55340
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:48:07.128927+00:00
-- url     : https://prove2.me/submissions/3db7cedd-4fc6-454d-b967-0ed89890a302

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^32 + 1 ≡ 0 [ZMOD 641] := by
  decide
