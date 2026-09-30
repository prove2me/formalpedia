-- Prove2me | solution 1 for lean_workbook_plus_7684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:38:31.74169+00:00
-- url     : https://prove2.me/submissions/3a2e0ee7-e820-40ce-8675-b3f826f83ddf

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 40 ≡ 1 [ZMOD 31] := by
  decide
