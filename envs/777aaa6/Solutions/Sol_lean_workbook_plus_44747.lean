-- Prove2me | solution 1 for lean_workbook_plus_44747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:48:06.067188+00:00
-- url     : https://prove2.me/submissions/22229b80-c834-4d05-8e38-c8339814a004

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 11 ^ 10 ≡ 1 [ZMOD 100] := by
  decide
