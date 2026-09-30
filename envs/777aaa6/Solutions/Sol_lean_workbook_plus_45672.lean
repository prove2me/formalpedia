-- Prove2me | solution 1 for lean_workbook_plus_45672
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:48.424732+00:00
-- url     : https://prove2.me/submissions/32e52c9a-6c6c-4ffb-9a8b-92d65c058ad5

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5 ^ 4 ≡ 1 [ZMOD 16] := by
  decide
