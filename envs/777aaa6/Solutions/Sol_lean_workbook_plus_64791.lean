-- Prove2me | solution 1 for lean_workbook_plus_64791
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:39.941097+00:00
-- url     : https://prove2.me/submissions/33a5f7dc-7756-4760-8695-34be960a5f78

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 6^42 ≡ 1 [ZMOD 43] := by
  decide
