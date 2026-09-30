-- Prove2me | solution 1 for lean_workbook_plus_31217
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:09.373018+00:00
-- url     : https://prove2.me/submissions/6cc447b5-95d6-4447-95af-5f2bd96b0352

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 1000000 ≡ 1 [ZMOD 7] := by
  decide
