-- Prove2me | solution 1 for lean_workbook_plus_25912
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:10.524093+00:00
-- url     : https://prove2.me/submissions/ff045d12-1695-4494-9a60-c738f9fbce10

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 ^ 20 ≡ 1 [ZMOD 25] := by
  decide
