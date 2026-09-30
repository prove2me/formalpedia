-- Prove2me | solution 1 for lean_workbook_plus_19860
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:50:00.115931+00:00
-- url     : https://prove2.me/submissions/0280ea73-ae61-416c-8ccf-45f1e13befff

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 3 ^ 20 ≡ 1 [ZMOD 100] := by
  decide
