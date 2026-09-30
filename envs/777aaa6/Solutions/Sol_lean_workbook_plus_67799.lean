-- Prove2me | solution 1 for lean_workbook_plus_67799
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:27.685732+00:00
-- url     : https://prove2.me/submissions/e388f3b1-6f9f-44f8-8968-431ca5461b90

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 21 ≡ 1 [ZMOD 7] := by
  decide
