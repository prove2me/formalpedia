-- Prove2me | solution 1 for lean_workbook_plus_59734
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:15.463441+00:00
-- url     : https://prove2.me/submissions/092b0cd8-783b-47f3-9ae8-fe7ba6a5860e

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 28 ≡ 1 [ZMOD 29] := by
  decide
