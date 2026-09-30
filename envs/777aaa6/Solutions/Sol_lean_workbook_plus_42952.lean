-- Prove2me | solution 1 for lean_workbook_plus_42952
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:39.631535+00:00
-- url     : https://prove2.me/submissions/5a84fbe2-a6e9-4697-804f-418178ec93c8

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 12 + 13 ≡ 7 + 8 [ZMOD 5] := by
  decide
