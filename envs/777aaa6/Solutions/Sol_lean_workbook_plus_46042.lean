-- Prove2me | solution 1 for lean_workbook_plus_46042
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:38.950278+00:00
-- url     : https://prove2.me/submissions/77d205e0-7b76-4cd0-ac0c-27385edea9de

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7^4 ≡ 1 [ZMOD 400] := by
  decide
