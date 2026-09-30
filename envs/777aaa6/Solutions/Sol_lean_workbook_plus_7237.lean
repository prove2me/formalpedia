-- Prove2me | solution 1 for lean_workbook_plus_7237
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:16:45.841701+00:00
-- url     : https://prove2.me/submissions/dc6837cb-900b-4d64-a200-a571babf67d9

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^6 ≡ -1 [ZMOD 13] := by
  decide
