-- Prove2me | solution 1 for lean_workbook_plus_44975
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:17:49.719217+00:00
-- url     : https://prove2.me/submissions/ba273e7a-bf2b-4eb0-89f0-3e5c6e541e07

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 9^6 ≡ 1 [ZMOD 130] := by
  decide
