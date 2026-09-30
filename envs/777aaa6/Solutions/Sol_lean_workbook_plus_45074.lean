-- Prove2me | solution 1 for lean_workbook_plus_45074
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:18:08.463517+00:00
-- url     : https://prove2.me/submissions/77a89023-2d70-4056-9529-6328ec7a52c9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 ^ 4 ≡ 1 [ZMOD 5] := by
  decide
