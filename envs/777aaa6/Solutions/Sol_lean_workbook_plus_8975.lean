-- Prove2me | solution 1 for lean_workbook_plus_8975
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:45.117087+00:00
-- url     : https://prove2.me/submissions/58796942-f052-41b6-88cc-e3913989ed90

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2015 ≡ -1 [ZMOD 3] := by
  decide
