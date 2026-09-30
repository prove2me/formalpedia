-- Prove2me | solution 1 for lean_workbook_plus_82436
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:16.884307+00:00
-- url     : https://prove2.me/submissions/655ba63a-ae50-4cdc-a8cc-8f91429ac236

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 8^8 ≡ 3^8 [ZMOD 11] := by
  decide
