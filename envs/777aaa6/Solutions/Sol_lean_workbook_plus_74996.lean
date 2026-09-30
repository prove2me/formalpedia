-- Prove2me | solution 1 for lean_workbook_plus_74996
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:59.726347+00:00
-- url     : https://prove2.me/submissions/a4a5296a-e505-459f-8b97-f6f84b1999d2

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 5^11 ≡ -1 [ZMOD 23] := by
  decide
